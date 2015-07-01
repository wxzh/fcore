{- |
Module      :  Z3Backend
Description :  The Z3 backend for symbolic
Copyright   :  (c) 2014—2015 The F2J Project Developers (given in AUTHORS.txt)
License     :  BSD3

Maintainer  :  Weixin Zhang <zhangweixinxd@gmail.com>
Stability   :  unstable
Portability :  portable

Symbolic evaluator will generates all possible execution paths for a given program. We use Z3 to kick out those infeasible execution paths.
-}

module Z3Backend where

import Debug.Trace
import           Control.Monad
import           Control.Monad.IO.Class       (liftIO)
import qualified Data.IntMap                  as IntMap
import           Data.Map                     (Map, fromList)
import qualified Data.Map                     as Map
import           Data.Maybe                   (fromJust)
import           Prelude                      hiding (EQ, GT, LT)
import           PrettyUtils
import qualified Src                          as S
import           SymbolicEvaluator
import           System.CPUTime
import qualified SystemFI                     as FI
import           Text.PrettyPrint.ANSI.Leijen
import           Z3.Monad                     hiding (Z3Env)
import           Z3ModelParser

data Z3Env = Z3Env { index             :: Int
                   , boolSort, intSort :: Sort
                   , constrDecls       :: Map.Map String FuncDecl
                   , adtSorts          :: Map.Map String Sort
                   , symVars           :: IntMap.IntMap AST
                   , funVars           :: IntMap.IntMap FuncDecl
                   , target            :: Doc -> SymValue -> Z3 ()
                   , evidence          :: IntMap.IntMap (Either Bool (String, [(Int, SymType)]))
                   }

explore :: Int -> FI.Expr () ExecutionTree -> IO ()
explore = traverse defaultTarget

counter :: Integer -> Int -> FI.Expr () ExecutionTree -> IO ()
counter time = traverse (counterTarget time)

-- Collcet and declare all datatype definitions in the expression
declareAllDatatypes :: Z3Env -> FI.Expr () ExecutionTree -> Z3 Z3Env
declareAllDatatypes = go
    where tree = Exp $ SBool True
          trees = repeat tree
      --  go (Data Rec databinds e1) = concatMap databinds ++ go e1
          go env (FI.Data S.NonRec [databind] e1) =
            do env' <- declareDatatype env 0 databind
               go env' e1
          go env (FI.If e1 e2 e3) = foldM go env [e1, e2, e3]
          go env (FI.PrimOp e1 _ e2) = foldM go env [e1, e2]
          go env (FI.Let _ e f) = foldM go env [e, f tree]
          go env (FI.TApp e1 _) = go env e1
          go env (FI.App e1 e2) = foldM go env [e1, e2]
          go env (FI.Constr _ es) = foldM go env es
          go env (FI.Case e1 alts) =
            do env' <- go env e1
               foldM (\acc (FI.ConstrAlt _ _ f) -> go acc (f trees)) env alts
          go env (FI.Lam _ _ e) = go env (e tree)
          go env (FI.BLam _ e) = go env (e ())
          go env (FI.Fix _ _ f _ _) = go env (f tree tree)
          go env (FI.LetRec _ _ binds body) =
            do env' <- foldM go env (binds trees)
               go env' (body trees)
          go env _ = return env

-- Declare a datatype, e.g. List: mkDatatype "List" [Nil, Cons]
declareDatatype :: Z3Env -> Int -> FI.DataBind () -> Z3 Z3Env
declareDatatype env recFlag (FI.DataBind name _ cs) =
    do sym <- mkStringSymbol name
       constrs <- mapM (declareConstructor env recFlag . transConstructor) (cs $ repeat ())
       sort <- mkDatatype sym constrs
       -- mapM_ delConstructor constrs
       return env { adtSorts = Map.insert name sort (adtSorts env) }

-- Declare a constructor, e.g. Cons: mkConstructor "Cons" "isCons" [("Cons_1", Just intSort, 0), ("Cons_2", Nothing, 0)]
declareConstructor :: Z3Env -> Int -> SConstructor -> Z3 Constructor
declareConstructor env recFlag (SConstructor name types datatype) =
    do constr_sym <- mkStringSymbol name
       recognizer_sym <- mkStringSymbol ("is" ++ name)
       param_syms <- mapM (\i -> mkStringSymbol $ name ++ "_" ++ show i) [1..length types]
       let param_triples = zipWith (\sym t -> if t == datatype
                                              then (sym, Nothing, recFlag)
                                              else (sym, Just $ type2sort env t, recFlag))
                           param_syms
                           types
       mkConstructor constr_sym recognizer_sym param_triples

-- Given a datatype sort, returns a list of constructor name and its funcdecl pair
getAdtConstrNameDeclPairs :: Sort -> Z3 [(String, FuncDecl)]
getAdtConstrNameDeclPairs adtSort =
    do decls <- getDatatypeSortConstructors adtSort
       mapM pairWithName decls

    where pairWithName decl =
              do name <- getSymbolString =<< getDeclName decl
                 return (name, decl)

traverse :: (Int -> Doc -> SymValue -> Z3 ())
         -> Int
         -> FI.Expr () ExecutionTree
         -> IO ()
traverse target stop e =
    evalZ3 $ do
      int <- mkIntSort
      bool <- mkBoolSort
      -- tvar <- mkStringSymbol "T" >>= mkUninterpretedSort -- for type parameters

      let (tree, i) = exec $ seval e -- i is the # of symbolic values
      let env = Z3Env { index = i
                      , intSort = int
                      , boolSort = bool
                      , adtSorts = Map.empty
                      , constrDecls = Map.empty
                      , symVars = IntMap.empty
                      , funVars = IntMap.empty
                      , target = target i
                      , evidence = IntMap.empty
                      }
      env' <- declareAllDatatypes env e
      constr_decls <- foldM (\acc sort ->
                                     do pairs <- getAdtConstrNameDeclPairs sort
                                        return $ Map.fromList pairs `Map.union` acc)
                       Map.empty
                      (Map.elems $ adtSorts env')
      (q, f, i) <- pathsZ3 env' { constrDecls = constr_decls } tree [] stop
      liftIO $ putDoc $ text "infeasible paths/total paths" <+> colon <+> parens ((text $ show i) <> char '/' <> (text . show $ f+i)) <> linebreak
      liftIO $ putDoc $ text "queries" <+> colon <+> text (show q) <> linebreak

defaultTarget :: Int -> Doc -> SymValue -> Z3 ()
defaultTarget _ cond e = liftIO $ putDoc $ cond <+> evalTo <+> pretty e <> linebreak

counterTarget :: Integer -> Int -> Doc -> SymValue -> Z3 ()
counterTarget startTime i cond (SBool False) =
    do liftIO $ getCPUTime >>= (\time -> putDoc $ (text . show $ (time - startTime) `div` (10^9)) <> text "ms" <> linebreak)
       liftIO $ putDoc $ cond <+> evalTo <+> text "False" <> linebreak
       withModel ((>>= (liftIO . putStrLn . counterExample i)) . showModel)
       return ()
counterTarget _ _ _ _ = return ()

pathsZ3 :: Z3Env -> ExecutionTree -> [Doc] -> Int -> Z3 (Int, Int, Int)
pathsZ3 _ _ _ stop | stop <= 0 = return (0, 0, 0)
pathsZ3 env (Exp e) conds _ =
    do target env (foldr1 combineWithAnd conds') e
       return (0, 1, 0)
    where conds' = reverse $ case conds of
                               [] -> conds ++ [text "True"] -- sole result
                               _ -> conds

pathsZ3 env (NewSymVar i typ t) conds stop =
    do ast <- declareVar env i typ
       let env' = either
                  (\x -> env{symVars = IntMap.insert i x (symVars env)})
                  (\x -> env{funVars = IntMap.insert i x (funVars env)})
                  ast
       pathsZ3 env' t conds stop

pathsZ3 env (Fork TBool e ts) conds stop =
  case e of
   SBool b -> case selectPattern b of
                   Just t -> pathsZ3 env t conds stop
                   _ -> return (0,0,0)
   SVar _ i _ ->
     case IntMap.lookup i evi of
      Just (Left b) -> case selectPattern b of
                        Just t -> pathsZ3 env t conds stop
                        _ -> error "selectPattern SVar"
      _ -> go i stop
   _ -> go (-1) $ stop-1
  where
    evi = evidence env
    cts = map (\(c,_,f) -> (toBool c, f [])) ts
    selectPattern b = lookup b cts
    go i stop =
      do ast <- assertProjs env e
         let assertBool (True, f) = local $ assert ast >> whenSat (pathsZ3 (if i >= 0 then env {evidence = IntMap.insert i (Left True) evi} else env) f (pretty e : conds) stop)
             assertBool (False, f) = local $ mkNot ast >>= assert >> whenSat (pathsZ3 (if i >= 0 then env {evidence = IntMap.insert i (Left False) evi} else env) f (prependNot (pretty e) : conds) stop)
         triples <- mapM assertBool cts
         return $ sumTriples triples

pathsZ3 env (Fork t e ts) conds stop =
  case e of
   SConstr c vs ->
     pathsZ3 env (selectPattern (sconstrName c) $ map Exp vs) conds stop
   SVar _ i _ ->
     case IntMap.lookup i (evidence env) of
      Just (Right (n, its)) -> pathsZ3 env (selectPattern n $ map (\(i,t) -> Exp $ SVar "x" i t) its) conds stop
      _ -> go i $ stop-1
   _ -> go (-1) (stop-1)
  where
    nfs = map (\(c,_,f) -> (sconstrName c, f)) ts
    selectPattern n = case lookup n nfs of
                       Just f -> f
                       _ -> error "selectPattern n"
    go i stop =
      do ast <- assertProjs env e
         triples <- mapM (local . assertConstructor ast) ts
         return $ sumTriples triples

      where assertConstructor :: AST -> (SConstructor, [S.Name], [ExecutionTree] -> ExecutionTree) -> Z3 (Int, Int, Int)
            assertConstructor ast (SConstructor name types _, vars, f) =
              let constr_decl = constrDecls env Map.! name
                  var_sorts = map (type2sort env) types
                  next_index = index env + length vars
                  var_ids = [index env .. next_index - 1]
              in do var_id_ast_pairs <- zipWithM declareVarSort var_sorts var_ids
                    let var_asts = map snd var_id_ast_pairs
                        env' = env { index = next_index, symVars = IntMap.fromList var_id_ast_pairs `IntMap.union` symVars env }
                        env'' = if i >= 0 then env' {evidence = IntMap.insert i (Right (name, zip var_ids types)) (evidence env') } else env'
                        cond = pretty e <+> equals <+> hsep (map text $ name : map (("x"++) . show) var_ids)

                    assert =<< mkEq ast =<< mkApp constr_decl var_asts
                    whenSat $ pathsZ3 env'' (f $ supply (repeat "x") var_ids) (cond : conds) stop

type2sort :: Z3Env -> SymType -> Sort
type2sort env TBool = boolSort env
type2sort _ (TFun _ _) = error "type2sort: Function type"
type2sort env (TData name) = case Map.lookup name $ adtSorts env of
                              Just s -> s
                              _ -> error $ "type2sort:" ++ name ++ show (adtSorts env)
type2sort env _ = intSort env -- both TAny will be instantiated as Int
-- type2sort env _ = tvarSort env

declareVar :: Z3Env -> Int -> SymType -> Z3 (Either AST FuncDecl)
declareVar env i (TFun tArgs tRes) =
    fmap Right (declareSymFun i (map (type2sort env) tArgs) (type2sort env tRes))
declareVar env i typ = fmap (Left . snd) $ declareVarSort (type2sort env typ) i

declareVarSort :: Sort -> Int -> Z3 (Int, AST)
declareVarSort s n =
    do x <- mkIntSymbol n
       c <- mkConst x s
       return (n, c)

declareSymFun :: Int -> [Sort] -> Sort -> Z3 FuncDecl
declareSymFun i args res =
    do f <- mkIntSymbol i
       mkFuncDecl f args res

-- assertProj :: AST -> (FuncDecl, AST) -> Z3 ()
-- assertProj app (f, arg) =
--     do ast <- mkApp f [app] >>= mkEq arg
--        assert ast

assertProjs :: Z3Env -> SymValue -> Z3 AST
assertProjs Z3Env {intSort = int, symVars = vars, funVars = funs, constrDecls = constrs} = go
    where go (SConstr c vs) =
              do asts <- mapM go vs
                 let decl = constrs Map.! sconstrName c
                 mkApp decl asts
          go (SVar _ i _) = return $ vars IntMap.! i
          go (SInt i) = mkInt (fromInteger i) int
          go (SBool True) = mkTrue
          go (SBool False) = mkFalse
          go (SOp op v1 v2) =
              do x1 <- go v1
                 x2 <- go v2
                 case op of
                   ADD -> mkAdd [x1, x2]
                   SUB -> mkSub [x1, x2]
                   MUL -> mkMul [x1, x2]
                   OR -> mkOr [x1, x2]
                   AND -> mkAnd [x1, x2]
                   DIV -> mkDiv x1 x2
                   LT -> mkLt x1 x2
                   LE -> mkLe x1 x2
                   GT -> mkGt x1 x2
                   GE -> mkGe x1 x2
                   EQ -> mkEq x1 x2
                   NEQ -> do ast <- mkEq x1 x2
                             mkNot ast
          go (SApp v1 v2) = symFun v1 [v2]
          go (SFun{}) = error "symValueZ3 of SFun"

          symFun :: SymValue -> [SymValue] -> Z3 AST
          symFun (SApp v1 v2) vs = symFun v1 (v2:vs)
          symFun (SVar _ i _) vs =
              do args <- mapM go vs
                 let f = funs IntMap.! i
                 mkApp f args
          symFun _ _ = error "symFun"

whenSat :: Z3 (Int, Int, Int) -> Z3 (Int, Int, Int)
whenSat m =
    do b <- fmap res2bool check
       if b
         then do (q, f, i) <- m
                 return (q+1, f, i)
         else return (1, 0, 1)

res2bool :: Result -> Bool
res2bool Sat = True
res2bool Unsat = False
res2bool Undef = error "res2bool: Undef"

toBool :: SConstructor -> Bool
toBool (SConstructor "True" [] TBool) = True
toBool (SConstructor "False" [] TBool) = False
toBool (SConstructor n ts t) = error $ "toBool " ++ n ++ (concatMap show ts) ++ show t

sumTriples = foldr (\(q,f,i) (qacc,facc,iacc) -> (qacc+q,facc+f,iacc+i)) (0,0,0)
