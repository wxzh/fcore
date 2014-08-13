{-# OPTIONS_GHC -fwarn-unused-binds #-}
{-# LANGUAGE RecordWildCards #-}

{- "GHC type checks programs in their original Haskell form before the desugarer converts
   them into Core code. This complicates the type checker as it has to handle the much more
   verbose Haskell AST, but it improves error messages, as those message are based on the
   same structure that the user sees." -}

module ESF.TypeCheck
  ( infer
  ) where

import ESF.Syntax

import JVMTypeQuery

import System.IO
import System.Process

import Control.Monad
import Control.Monad.Trans.Error

import Text.PrettyPrint.Leijen

import Data.Maybe       (fromJust)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.IO.Class (liftIO)

-- https://www.cs.princeton.edu/~dpw/papers/tal-toplas.pdf

-- The monad for typechecking
type TCMonad = ErrorT (TypeError Name) IO

data TypeError e
  = NotInScope        { msg       :: String }
  | General           { msg       :: String }
  | NotAJVMType       { msg       :: String }
  | NoSuchConstructor { argsInfo  :: [Expr e] }
  | NoSuchMethod      { mName     :: String   
                      , argsInfo  :: [Expr e]
                      }
  | Mismatch          { term      :: Expr e
                      , expected  :: Type
                      , actual    :: Type
                      }

instance Error e => Error (TypeError e) where
--   strMsg 

instance Pretty e => Pretty (TypeError e) where
  pretty Mismatch{..} =
    text "Type mismatch:" <$>
    text "Expected type:" <+> pretty expected <$>
    text "  Actual type:" <+> pretty actual <$>
    text "In the expression:" <+> pretty term
  pretty NotInScope{..}  = text "Not in scope:" <+> string msg
  pretty General{..}     = string msg
  pretty (NotAJVMType c) = text (q c) <+> text "is not a JVM type"


q :: Name -> String
q x = "`" ++ x ++ "'"

--throwE :: TypeError Name -> TCMonad ()
--throwE te = throwError . show . pretty te

checkWellformed :: (Handle, Handle) -> TypeContext -> Type -> TCMonad ()
checkWellformed io _ (JClass c) = do ok <- liftIO $ isJVMType io c
                                     unless ok (throwError (NotAJVMType c))
checkWellformed _  d t =
  let s = freeTyVars t `Set.difference` d in
  unless (Set.null s) $
    throwError NotInScope { msg = "type variable " ++ q (head $ Set.toList s) }


infer :: RdrExpr -> TCMonad (TcExpr, Type)
infer e = do (Just inp, Just out, _, proch) <- liftIO $ createProcess (proc "java" ["Test"]){std_in = CreatePipe, std_out = CreatePipe}
             liftIO $ hSetBuffering inp NoBuffering
             liftIO $ hSetBuffering out NoBuffering
             ret <- inferWith (inp, out) (Set.empty, Map.empty) e
             liftIO $ terminateProcess proch
             return ret


inferWith :: (Handle, Handle) -> (TypeContext, ValueContext) -> RdrExpr -> TCMonad (TcExpr, Type)
inferWith io (d, g) = go
  where
    go (Var x) = case Map.lookup x g of
                   Just t  -> return (Var (x,t), t)
                   Nothing -> throwError NotInScope { msg = "variable " ++ q x }

    go (Lit (Integer n)) = return (Lit (Integer n), Int)

    go (App e1 e2) = do
      (e1', t)  <- go e1
      (e2', t') <- go e2
      case t of
        Fun t1 t2 | t' `alphaEqTy` t1 -> return (App e1' e2', t2) -- TODO: need var renaming?
        Fun t1 _ -> throwError Mismatch { term = e2, expected = t1, actual = t' }
        _        -> throwError Mismatch { term = e1
                                    , expected = Fun t' (TyVar "_")
                                    , actual = t
                                    }

    go (BLam a e)
      | a `Set.member` d = throwError General { msg = "This type variable " ++ q a ++
                                                  " shadows an existing type variable" ++
                                                  " in an outer scope"
                                          }
      | otherwise        = do (e', t) <- inferWith io (Set.insert a d, g) e
                              return (BLam a e', Forall a t)

    go (Lam (x,t) e) = do
      checkWellformed io d t
      (e', t') <- inferWith io (d, Map.insert x t g) e
      return (Lam (x,t) e', Fun t t')

    {-
      τ ok in Δ   Δ;Γ ⊢ e : ∀α. τ'
      ----------------------------
          Δ;Γ ⊢ e[τ] : τ'[τ/α]
    -}
    go (TApp e t) = do
      checkWellformed io d t
      (e', t1) <- go e
      case t1 of
        Forall a t' -> return (TApp e' t, substFreeTyVars (a, t) t')
        _           -> throwError Mismatch { term     = TApp e t
                                       , expected = Forall "_" (TyVar "_")
                                       , actual   = t1
                                       }

    go (Tuple es)
      | length es < 2 = invariantFailed
                          "inferWith"
                          ("fewer than two items in the tuple " ++ show (Tuple es))
      | otherwise     = do (es', ts) <- mapAndUnzipM go es
                           return (Tuple es', Product ts)

    go (Proj e i) = do
      (e', t) <- go e
      case t of
        Product ts ->
          if 1 <= i && i <= length ts
            then return (Proj e' i, ts !! (i-1))
            else throwError General { msg = "Index too large in projection" }
        _          ->
          throwError General { msg = "Projection of a term that is not of product type" }

    go (PrimOp e1 op e2) = do
      (e1', t1) <- go e1
      (e2', t2) <- go e2
      case (t1, t2) of
        (Int, Int) -> return (PrimOp e1' op e2', Int)
        (Int, _  ) -> throwError Mismatch { term = e2, expected = Int, actual = t2 }
        (_  , _  ) -> throwError Mismatch { term = e1, expected = Int, actual = t1 }

    go (If0 e1 e2 e3) = do
      (e1', t1) <- go e1
      case t1 of
        Int ->
          do (e2', t2) <- go e2
             (e3', t3) <- go e3
             if t2 `alphaEqTy` t3
               then return (If0 e1' e2' e3', t2)
               else throwError Mismatch { term = e3, expected = t2, actual = t3 }
        JClass "java.lang.Integer" ->
          do (e2', t2) <- go e2
             (e3', t3) <- go e3
             if t2 `alphaEqTy` t3
               then return (If0 e1' e2' e3', t2)
               else throwError Mismatch { term = e3, expected = t2, actual = t3 }
        _   -> throwError Mismatch { term = e1, expected = Int, actual = t1 }

    go (Let NonRec bs e) = do
      checkBinds io d bs
      bs' <-
        forM bs (\Bind{..} ->
          do let d_local = Set.fromList bindTargs
                 g_local = Map.fromList bindArgs
             (rhs, inferredRhsTy) <- inferWith io (d_local `Set.union` d, g_local `Map.union` g) bindRhs
             case bindRhsAnnot of
               Nothing -> return ()
               Just claimedRhsTy ->
                 unless (claimedRhsTy `alphaEqTy` inferredRhsTy) $
                   throwError Mismatch { term = bindRhs, expected = claimedRhsTy, actual = inferredRhsTy }
             return ( bindId
                    , wrap Forall bindTargs $ wrap Fun [t | (_,t) <- bindArgs] inferredRhsTy
                    , wrap BLam bindTargs $ wrap Lam bindArgs rhs
                    ))
      let (fs, ts, _es) = unzip3 bs'
      (e', t) <- inferWith io (d, Map.fromList (zip fs ts) `Map.union` g) e
      return (LetOut NonRec bs' e', t)

    go (Let Rec bs e) = do
      checkBinds io d bs
      sigs <-
        liftM Map.fromList $
          forM bs (\Bind{..} ->
            case bindRhsAnnot of
              Nothing    -> throwError General { msg = "Missing type annotation for the right hand side" }
              Just rhsTy -> return (bindId, wrap Forall bindTargs $ wrap Fun [t | (_,t) <- bindArgs] rhsTy))
      bs' <-
        forM bs (\Bind{..} ->
          do let d_local = Set.fromList bindTargs
                 g_local = Map.fromList bindArgs
             (rhs, inferredRhsTy) <- inferWith io (d_local `Set.union` d, g_local `Map.union` sigs `Map.union` g) bindRhs
             let claimedRhsTy = fromJust bindRhsAnnot
             unless (claimedRhsTy `alphaEqTy` inferredRhsTy) $
               throwError Mismatch { term = bindRhs, expected = claimedRhsTy, actual = inferredRhsTy }
             return ( bindId
                    , wrap Forall bindTargs $ wrap Fun [t | (_,t) <- bindArgs] inferredRhsTy
                    , wrap BLam bindTargs $ wrap Lam bindArgs rhs
                    ))
      let (fs, ts, _es) = unzip3 bs'
      (e', t) <- inferWith io (d, Map.fromList (zip fs ts) `Map.union` g) e
      return (LetOut Rec bs' e', t)

    go (LetOut{..}) = error (invariantFailed "inferWith" (show (LetOut{..} :: RdrExpr)))

    go (JNewObj c args) = do ok <- liftIO $ isJVMType io c
                             if ok
                               then do (args', typs') <- mapAndUnzipM go args
                                       strArgs <- checkJavaArgs typs'
                                       ok' <- liftIO $ hasConstructor io c strArgs
                                       if ok'
                                         then return (JNewObj c args', JClass c)
                                         else throwError (NoSuchConstructor args)
                               else throwError (NotAJVMType c)

    go (JMethod e m args) = do (e', t') <- go e
                               case t' of JClass cls -> do (args', typs') <- mapAndUnzipM go args
                                                           strArgs <- checkJavaArgs typs'
                                                           retName <- liftIO $ methodRetType io cls m strArgs
                                                           case retName of Just r  -> return (JMethod e' m args', JClass r)
                                                                           Nothing -> throwError NoSuchMethod { mName = m, argsInfo = args }
                                          otherType  -> throwError $ NotAJVMType $ show otherType


checkJavaArgs :: [Type] -> TCMonad [Name]
checkJavaArgs = mapM check
  where
    check (JClass name) = return name
    check otherType     = throwError $ NotAJVMType $ show otherType 


checkBinds :: (Handle, Handle) -> TypeContext -> [Bind Name] -> TCMonad ()
checkBinds io d bs =
  do checkForDup "identifiers" (map bindId bs)
     forM_ bs (\Bind{..} ->
       do checkForDup "type arguments" bindTargs
          checkForDup "arguments"      [x | (x, _) <- bindArgs]
          forM_ bindArgs (\(_,t) ->
            do let d' = Set.fromList bindTargs `Set.union` d
               checkWellformed io d' t))


checkForDup :: String -> [String] -> TCMonad ()
checkForDup what xs =
  case findFirstDup xs of
    Just x  -> throwError General { msg = "Duplicate " ++ what ++ ": " ++ q x }
    Nothing -> return ()


findFirstDup :: Ord a => [a] -> Maybe a
findFirstDup xs = go xs Set.empty
  where
    go []      _ = Nothing
    go (x:xs') s = if Set.member x s
                     then Just x
                     else go xs' (Set.insert x s)