{- |
Module      :  SymbolicEvaluator
Description :  Symbolic evaluator for Core
Copyright   :  (c) 2014—2015 The F2J Project Developers (given in AUTHORS.txt)
License     :  BSD3

Maintainer  :  Weixin <zhangweixinxd@gmail.com>
Stability   :  experimental
Portability :  portable

-}

module SymbolicEvaluator where

import           Control.Monad.Fix            (fix)
import           Data.Maybe
import qualified Language.Java.Syntax         as J (Op (..))
import           Panic
import           Prelude                      hiding (EQ, GT, LT)
import           PrettyUtils
import qualified Src                          as S
import           SystemFI
import           Text.PrettyPrint.ANSI.Leijen
import           Unsafe.Coerce

instance Show (Type t) where
  show = show . prettyType . unsafeCoerce

instance Show (Expr t e) where
  show = show . prettyExpr . unsafeCoerce

data Value = VInt Integer
           | VBool Bool
           | VConstr S.ReaderId [Value]
           | VFun (Value -> Value)

-- big-step interpreter
eval :: Expr () Value -> Value
eval (Var _ x) = x
eval (Lit x) =
    case x of
      S.Int n -> VInt n
      S.Bool b -> VBool b
      _ -> panic "Lit type unknown"
eval (Lam _ _ f) = VFun (eval . f)
eval (Let _ e f) = eval . f . eval $ e
eval (App e1 e2) =
    case eval e1 of
      VFun f -> f (eval e2)
      _ -> panic "e1 is not a function"
eval (BLam _ f) = eval (f ())
eval (TApp e1 _) = eval e1
eval (If e1 e2 e3) =
       case eval e1 of
         VBool True -> eval e2
         VBool False -> eval e3
         _ -> panic "e1 is not a boolean"
eval (PrimOp e1 op e2) =
       case (eval e1, eval e2) of
         (VInt a, VInt b) ->
             case op of
               -- arithmetic operations
               S.Arith J.Add -> VInt $ a + b
               S.Arith J.Mult -> VInt $ a * b
               S.Arith J.Sub -> VInt $ a - b
               S.Arith J.Div -> VInt $ a `div` b
               -- comparison operations
               S.Compare J.Equal -> VBool $ a == b
               S.Compare J.NotEq -> VBool $ a /= b
               S.Compare J.LThan -> VBool $ a < b
               S.Compare J.LThanE -> VBool $ a <= b
               S.Compare J.GThan -> VBool $ a > b
               S.Compare J.GThanE -> VBool $ a >= b
               -- _ -> simplified
         (VBool a, VBool b) ->
             case op of
               -- logic operations
               S.Logic J.CAnd -> VBool $ a && b
               S.Logic J.COr -> VBool $ a || b
               S.Compare J.Equal -> VBool $ a == b
               S.Compare J.NotEq -> VBool $ a /= b
               _ -> panic $ "Unknown op" ++ show op
         _ -> panic "e1 and e2 should be either Int or Bool simutaneously"
eval g@(Fix _ _ f _ _) = VFun $ eval . f (eval g)
eval (LetRec _ _ binds body) = eval . body . fix $ map eval . binds
eval (Data _ _ e) = eval e
eval (Constr c es) = VConstr (constrName c) (map eval es)
eval (Case e alts) =
    case eval e of
      VConstr n vs -> eval $ fromJust (lookup n table) vs
    where table = map (\(ConstrAlt c _ f) -> (constrName c, f)) alts
eval e = panic $ show e ++ " Can not be evaled"

data SConstructor = SConstructor {sconstrName :: S.ReaderId, sconstrParams :: [SymType], sconstrDatatype :: SymType}
                  deriving Eq

data ExecutionTree = Exp SymValue
                   -- | Fork ExecutionTree SymValue ExecutionTree
                   | Fork SymType SymValue [(SConstructor, [S.ReaderId], [ExecutionTree] -> ExecutionTree)]
                   | NewSymVar Int SymType ExecutionTree

data SymType = TInt
             | TBool
             | TFun [SymType] SymType
             | TData S.ReaderId
             | TAny S.ReaderId
               deriving (Show, Eq)

data SymValue = SVar S.ReaderId Int SymType -- free variables
              | SInt Integer
              | SBool Bool
              | SApp SymValue SymValue
              | SOp Op SymValue SymValue
              | SFun S.ReaderId (ExecutionTree -> ExecutionTree) SymType
              | SConstr SConstructor [SymValue]

data Op = ADD
        | MUL
        | SUB
        | DIV
        | LT
        | LE
        | GT
        | GE
        | EQ
        | NEQ
        | OR
        | AND

-- Add index to SVars and apply symbolic value to top-level closure
exec :: ExecutionTree -> (ExecutionTree, Int)
exec = go 0
    where go i (Exp (SFun n f t)) =
              case go (i+1) (f . Exp $ SVar n i t) of
                (e', i') -> (NewSymVar i t e', i')
          go i e = (e, i)

-- symbolic evaluation
seval :: Expr () ExecutionTree -> ExecutionTree
seval (Var _ x) = x
seval (Lit x) =
    case x of
      S.Int n -> Exp $ SInt n
      -- S.Bool b -> Exp $ SBool b
seval (PrimOp e1 op e2) = merge (lift $ transOp op) [seval e1, seval e2]
seval (Lam n t f) = Exp $ SFun n (seval . f) (transType t)
seval (Let _ e f) = seval . f $ seval e
seval (App e1 e2) = treeApply (seval e1) (seval e2)
seval (BLam _ f) =  seval $ f ()
seval (TApp e _) = seval e
seval g@(Fix _ n f t _) = Exp $ SFun n (seval . f (seval g)) (transType t)
seval (LetRec _ _ binds body) = seval . body . fix $ map seval . binds
seval (Data _ _ e) = seval e
seval (Constr c es) =
  case c of
   Constructor "True" _ -> Exp $ SBool True
   Constructor "False" _ -> Exp $ SBool False
   _ -> merge (SConstr $ transConstructor c) (map seval es)
seval (Case e alts) = propagate (transType $ last ts) (seval e) (map (\(ConstrAlt c ns f) -> (transConstructor c, ns, seval . f)) alts)
  where ConstrAlt (Constructor _ ts) _ _ = head alts
seval e = panic $ "seval: " ++ show e

transConstructor :: Constructor () -> SConstructor
transConstructor (Constructor n ts) = SConstructor n (init ts') (last ts')
    where ts' = map transType ts

propagate :: SymType ->
             ExecutionTree ->
             [(SConstructor, [S.ReaderId], [ExecutionTree] -> ExecutionTree)] ->
             ExecutionTree
propagate dt (Exp e) ts = Fork dt e ts
propagate dt' (Fork dt e ts) ts' = Fork dt e [(c, ns, \es -> propagate dt' (f es) ts')| (c,ns,f) <- ts]
propagate dt (NewSymVar i typ t) ts = NewSymVar i typ (propagate dt t ts)

transType :: Type () -> SymType
transType (JClass t) = jname2symtype t
transType (Fun t1 t2) = TFun [transType t1] (transType t2)
transType (Datatype "Bool" _ _) = TBool
transType (Datatype n _ _) = TData n
transType (TVar n _) = TAny n
transType t = panic $ "transType: " ++ show t

transOp :: S.Operator -> Op
transOp op =
    case op of
        -- arithmetic operations
        S.Arith J.Add -> ADD
        S.Arith J.Mult -> MUL
        S.Arith J.Sub -> SUB
        S.Arith J.Div -> DIV

        -- comparison operations
        S.Compare J.Equal -> EQ
        S.Compare J.NotEq -> NEQ
        S.Compare J.LThan -> LT
        S.Compare J.LThanE -> LE
        S.Compare J.GThan -> GT
        S.Compare J.GThanE -> GE

        -- logic operations
        S.Logic J.CAnd -> AND
        S.Logic J.COr -> OR

jname2symtype :: String -> SymType
jname2symtype "java.lang.Integer" = TInt
-- jname2symtype "java.lang.Boolean" = TBool
jname2symtype s = panic $ "str2stype: unsupported java type " ++ s

merge :: ([SymValue] -> SymValue) -> [ExecutionTree] -> ExecutionTree
merge f [] = Exp (f [])
merge f (Exp e : xs) = merge (\es -> f (e:es)) xs
merge f (Fork dt e ts : xs) = Fork dt e [(c, ns, \es -> merge f (g es : xs)) | (c,ns,g) <- ts]
merge f (NewSymVar i typ tree : xs) = NewSymVar i typ (merge f (tree:xs))

lift :: Op -> [SymValue] -> SymValue
lift op vs =
    case (v1, v2) of
     (SInt i1, SInt i2) ->
       case op of
        ADD -> SInt (i1 + i2)
        MUL -> SInt (i1 * i2)
        DIV -> SInt (i1 `div` i2)
        SUB -> SInt (i1 - i2)
        EQ  -> SBool (i1 == i2)
        NEQ -> SBool (i1 /= i2)
        GT  -> SBool (i1 > i2)
        LT  -> SBool (i1 < i2)
        GE  -> SBool (i1 >= i2)
        LE  -> SBool (i1 <= i2)
     (SBool b1, SBool b2) ->
       case op of
        EQ  -> SBool (b1 == b2)
        NEQ -> SBool (b1 /= b2)
        AND -> SBool (b1 && b2)
        OR  -> SBool (b1 || b2)
     _ -> SOp op v1 v2
    where v1 = vs !! 0
          v2 = vs !! 1

treeApply :: ExecutionTree -> ExecutionTree -> ExecutionTree
treeApply (Exp e) t =
    case e of
      SVar n i typ -> apply (SApp (SVar n i typ)) t
      SFun _ f _ -> f t
treeApply (Fork dt e ts) t = Fork dt e [(c, ns, \es -> treeApply (f es) t) | (c,ns,f) <- ts]
treeApply (NewSymVar i typ t1) t2 = NewSymVar i typ (treeApply t1 t2)

apply :: (SymValue -> SymValue) -> ExecutionTree -> ExecutionTree
apply f (Exp e) = Exp (f e)
apply f (Fork dt e ts) = Fork dt e [(c, ns, apply f . g)| (c,ns,g) <- ts]
apply f (NewSymVar i typ t) = NewSymVar i typ (apply f t)

instance Pretty Value where
    pretty (VFun _) = text "<<func>>"
    pretty (VInt x) = integer x
    pretty (VBool b) = bool b
    pretty (VConstr n vs) = fillSep $ text n : map pretty vs

instance Pretty Op where
    pretty op =
        text $ case op of
                 ADD -> "+"
                 MUL -> "*"
                 SUB -> "-"
                 DIV -> "/"
                 LT -> "<"
                 LE -> "<="
                 GT -> ">"
                 GE -> ">="
                 EQ -> "=="
                 NEQ -> "/="
                 OR -> "||"
                 AND -> "&&"

instance Pretty SymValue where
    -- pretty (SVar n i _) = text n <> int i
    pretty (SVar _ i _) = text "x" <> int i
    -- pretty (SVar n _ _) = text n
    pretty (SInt i) = integer i
    pretty (SBool b) = bool b
    pretty (SApp e1 e2) = pretty e1 <+> pretty e2
    pretty (SOp op e1 e2) = parens $ pretty e1 <+> pretty op <+> pretty e2
    pretty (SFun{}) = text "<<fun>>"
    pretty (SConstr c []) = text (sconstrName c)
    pretty (SConstr c es) = parens $ hsep $ text (sconstrName c) : map pretty es

instance Pretty ExecutionTree where
    pretty t = fst $ prettyTree t (text "True") 5

prettyTree :: ExecutionTree -> Doc -> Int -> (Doc, Int)
prettyTree _ _ 0 = (empty, 0)
prettyTree (Exp e) s stop = (s <+> evalTo <+> pretty e <> linebreak, stop - 1)
prettyTree (Fork _ e ts) s stop =
    foldl (\(sacc, i) (c,ns,f) ->
               let (snew, i') = prettyTree (f $ supply ns [1..]) (s <+> text "&&" <+> pretty e <+> equals <+> hsep (map text $ sconstrName c : ns)) i
               in (sacc <> snew, i'))
       (empty, stop)
       ts
prettyTree (NewSymVar _ _ t) s stop = prettyTree t s stop

supply :: [S.ReaderId] -> [Int] -> [ExecutionTree]
supply ns ids = zipWith (\i n -> Exp $ SVar n i TInt) ids ns

-- genVars n = map (text . ("x"++) . show) [1..n]

fun e = fst . exec . seval $ e
