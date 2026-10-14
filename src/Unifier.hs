{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module Unifier where

import Control.Lens (Field1 (_1), Field2 (_2), Field3 (_3), Getting, over, preview, set, unsnoc, (.=), (^.))
import Control.Monad (forM, forM_, unless, when)
import Data.Generics.Labels ()
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, mapMaybe)
import Data.Monoid (First)
import Data.Set qualified as Set
import Effectful (Eff, IOE, MonadIO (liftIO), runEff, (:>))
import Effectful.NonDet (runNonDet)
import Effectful.NonDet qualified as ND
import Effectful.Reader.Static qualified as R
import Effectful.State.Static.Local qualified as S
import GHC.Generics (Generic)
import Prettyprinter qualified as PP

import Control.Lens qualified as S
import Data.Foldable (asum)
import Data.Function (on)
import Data.List (find)
import Unifier.Types

exprSubst :: Binder -> Term -> Term -> Term
exprSubst b replacement = go
 where
  go (App a b) = App (go a) (go b)
  go (Constant c) = Constant c
  -- Not sure about recursion here, depending on whether types have terms and
  -- whether the scopes are separate...
  go (Forall (x, τ₁) τ₂) = Forall (x, go τ₁) (go τ₂)
  go (Lambda (x, τ) body)
    | x == b = body
    | otherwise = Lambda (x, τ) (go body)
  go (MetaVar m ss) = error "TODO" -- TODO: add to suspended substitution
  go (Var v)
    | v == b = replacement
    | otherwise = Var v

betaReduction :: Reducer es
betaReduction (App (Lambda (x, τ) t) u) = return (exprSubst x t u)
betaReduction (Constant c) = return (Constant c)
betaReduction (Forall (x, τ₁) τ₂) = do
  τ₁' <- betaReduction τ₁
  τ₂' <- betaReduction τ₂
  return $ Forall (x, τ₁') τ₂'
betaReduction (Lambda (x, τ) body) = do
  τ' <- betaReduction τ
  body' <- betaReduction body
  return $ Lambda (x, τ') body
betaReduction (MetaVar mv ss) = return $ MetaVar mv ss -- do we need to reduce in substs?
betaReduction (Var v) = return $ Var v

weakHeadBeta :: Reducer es
weakHeadBeta (App (Lambda (x, τ) t) u) =
  return (exprSubst x t u)
weakHeadBeta _ = ND.emptyEff

weakHeadZeta :: Reducer es
weakHeadZeta (Let (x, u, τ) t) =
  return (exprSubst x t u)
weakHeadZeta _ = ND.emptyEff

-- weakHeadIota :: Reducer es
-- weakHeadIota _ = ND.emptyEff

-- weakHeadTheta :: Reducer es
-- weakHeadTheta _ = ND.emptyEff

weakHeadBetaZetaIotaTheta :: Reducer es
weakHeadBetaZetaIotaTheta t =
  ND.sumEff
    [ weakHeadBeta t
    , weakHeadZeta t
    -- , weakHeadIota t
    -- , weakHeadTheta t
    ]

weakHeadLetExpansion :: Reducer es
weakHeadLetExpansion _ = ND.emptyEff

weakHeadExpandLocalDef :: Reducer es
weakHeadExpandLocalDef (Var x) = lookupVarDef x
weakHeadExpandLocalDef _ = ND.emptyEff

weakHeadExpandMetaVariable :: Reducer es
weakHeadExpandMetaVariable (MetaVar x σ) = do
  _Σ <- S.gets metaContext
  case lookupMetaDeclForMetaVar x _Σ of
    Nothing -> ND.emptyEff
    Just (_, _T, ψ) -> error "Implement substitution" -- subst σ ψ t
    -- TODO: emptyEff or succeed without doing anything?
weakHeadExpandMetaVariable _ = ND.emptyEff

weakHeadExpand :: Reducer es
weakHeadExpand t =
  ND.sumEff
    [ weakHeadExpandLocalDef t
    , weakHeadExpandMetaVariable t
    -- , weakHeadExpandGlobalConstant t
    ]

metaDeltaR :: Unifier es
metaDeltaR t u = do
  u' <- weakHeadExpandMetaVariable u
  unify t u'

lamBetaR :: Unifier es
lamBetaR t u = do
  u' <- weakHeadBeta u
  unify t u'

letZetaR :: Unifier es
letZetaR t u = do
  u' <- weakHeadBeta u
  unify t u'

metaDeltaL :: Unifier es
metaDeltaL t u = do
  u' <- weakHeadExpandMetaVariable u
  unify t u'

lamBetaL :: Unifier es
lamBetaL t u = do
  u' <- weakHeadBeta u
  unify t u'

letZetaL :: Unifier es
letZetaL t u = do
  u' <- weakHeadBeta u
  unify t u'

manyWeakHeadBetaZetaIotaTheta :: Reducer es
manyWeakHeadBetaZetaIotaTheta t = do
  t' <- weakHeadBetaZetaIotaTheta t
  if t' == t
    then return t
    else manyWeakHeadBetaZetaIotaTheta t'

convertible :: Unifier es
convertible t u = do
  t' <- manyWeakHeadBetaZetaIotaTheta t
  u' <- manyWeakHeadBetaZetaIotaTheta u
  ND.emptyEff -- TODO

-- NOTE: if we don't care about universes, we're always in the Same-Same case
metaSameSame :: Unifier es
metaSameSame t u = do
  convertible t u

{- | Extracts nested application nodes, returns Nothing if there is no single
application node.  Arguments are in actual application order, i.e.:
extractApps (f a b c) = Just (f, [a, b, c])
-}
extractApps :: Term -> Maybe (Term, [Term])
extractApps = go []
 where
  go args (App f arg) = go (arg : args) f
  go [] _ = Nothing
  go args t = Just (t, args)

extractVarSpine :: Term -> Maybe (Term, [Variable])
extractVarSpine = go []
 where
  go vars (App t (Var v)) = go (v : vars) t
  go [] t = Nothing
  go vars t = Just (t, vars)

freeMetaVars :: Term -> Set.Set Variable
freeMetaVars (App a b) = freeMetaVars a `Set.union` freeMetaVars b
freeMetaVars (Constant _) = Set.empty
freeMetaVars (Forall (x, τ₁) τ₂) = freeMetaVars τ₁ `Set.union` freeMetaVars τ₂
freeMetaVars (Lambda (x, τ) body) = freeMetaVars τ `Set.union` freeMetaVars body
freeMetaVars (MetaVar mv ss) = Set.singleton mv -- what about ss?
freeMetaVars (Var v) = Set.empty

freeVars :: Term -> Set.Set Variable
freeVars (App a b) = freeVars a `Set.union` freeVars b
freeVars (Constant _) = Set.empty
freeVars (Forall (x, τ₁) τ₂) = freeVars τ₁ `Set.union` (freeVars τ₂ `Set.difference` Set.singleton x)
freeVars (Lambda (x, τ) body) = freeVars τ `Set.union` (freeVars body `Set.difference` Set.singleton x)
freeVars (MetaVar mv ss) = error "TODO"
freeVars (Var v) = Set.singleton v

removeEqualTails :: Term -> [Variable] -> (Term, [Variable])
removeEqualTails tL varsR = go tL (reverse varsR)
 where
  go (App tL (Var vL)) (vR : varsR)
    | vL == vR && not (vR `Set.member` freeVars tL) = go tL varsR
  go tL varsR = (tL, reverse varsR)

foo :: Meta -> Maybe (MetaVariable, Term, LocalContext)
foo = preview #_MetaDecl

isMetaDeclForMetaVar :: MetaVariable -> Meta -> Bool
isMetaDeclForMetaVar mv = (== Just mv) . preview (#_MetaDecl . _1)

asSuspendedSubstitutionOfVariables :: SuspendedSubstitution -> Maybe [Variable]
asSuspendedSubstitutionOfVariables = traverse (preview #_Var)

-- TODO: check the order of variables
asMetaVarAppliedToVariables :: Term -> Maybe (MetaVariable, [Variable], [Variable])
asMetaVarAppliedToVariables (MetaVar mv ss) = do
  ss' <- asSuspendedSubstitutionOfVariables ss
  Just (mv, ss', [])
asMetaVarAppliedToVariables (App l (Var v)) = over _3 (v :) <$> asMetaVarAppliedToVariables l
asMetaVarAppliedToVariables _ = Nothing

findLocal :: (Local -> Bool) -> LocalContext -> Maybe Local
findLocal pred (LocalContext locals) = find pred locals

isLocalForVariable :: Variable -> Local -> Bool
isLocalForVariable v = (== v) . localBinder

lookupVarDef ::
  ND.NonDet :> es =>
  UnifierEffects es =>
  Variable ->
  Eff es Term
lookupVarDef v = do
  γ <- R.asks localContext
  local <- fromJustOrFail $ findLocal (isLocalForVariable v) γ
  fromJustOrFail $ preview (#_LocalDef . _2) local

lookupVarType ::
  ND.NonDet :> es =>
  UnifierEffects es =>
  Variable ->
  Eff es Typ
lookupVarType v = do
  γ <- R.asks localContext
  local <- fromJustOrFail $ findLocal (isLocalForVariable v) γ
  return $ localType local

metaInstR :: Unifier es
metaInstR t (asMetaVarAppliedToVariables -> Just (mv, ξ, ξ')) = do
  _Σ₀ <- S.gets metaContext
  (_, _T, ψ) <- fromJustOrFail $ lookupMetaDeclForMetaVar mv _Σ₀
  let (t', ξ₁) = removeEqualTails t ξ'
  t'' <- weakHeadBeta t'
  _Σ₁ <- prune mv (ξ <> ξ₁) t
  _U <- mapM lookupVarType ξ₁
  t''' <- error "TODO"
  return ()
metaInstR t _ = ND.emptyEff

-- | @asApps (App a (App b c))@ should be @(a, [b, c])@
asApps :: Term -> (Term, [Term])
asApps (App l r) = (<> [r]) <$> asApps l
asApps t = (t, [])

metaFirstOrderR :: Unifier es
metaFirstOrderR a@(App _ _) (asApps -> (MetaVar x σ, tn)) = do
  let (u, umn) = asApps a
  error "TODO"
metaFirstOrderR _ _ = ND.emptyEff

findMetaVarDecl ::
  ND.NonDet :> es =>
  UnifierEffects es =>
  MetaVariable ->
  Eff es (MetaVariable, Term, LocalContext)
findMetaVarDecl mv = do
  _Σ₀ <- S.gets metaContext
  fromJustOrFail $ lookupMetaDeclForMetaVar mv _Σ₀

metaReducer :: Unifier es
metaReducer t u₀@(asApps -> (MetaVar u σ, ts)) = do
  (_, _T, ψ) <- findMetaVarDecl u
  t' <- weakHeadExpand t
  t'' <- weakHeadBetaZetaIotaTheta t'
  unify t'' u₀
metaReducer _ _ = ND.emptyEff

metaDelDeps :: Unifier es
metaDelDeps t u₀@(asApps -> (MetaVar x σ, u)) = do
  (_, _T, ψ) <- findMetaVarDecl x
  error "TODO"
metaDelDeps _ _ = ND.emptyEff

-- Instead of returning a MetaContext, this changes the ongoing one.  Could be
-- made to return it if we need to control this.
prune :: Prune es
prune x ξ t = do
  return ()

failIf :: ND.NonDet :> es => Bool -> Eff es ()
failIf = flip when ND.emptyEff

failUnless :: ND.NonDet :> es => Bool -> Eff es ()
failUnless = flip unless ND.emptyEff

fromJustOrFail :: ND.NonDet :> es => Maybe a -> Eff es a
fromJustOrFail = maybe ND.emptyEff pure

previewOrFail :: ND.NonDet :> es => Getting (First a) s a -> s -> Eff es a
previewOrFail l = fromJustOrFail . preview l

pruneConstant :: Prune es
pruneConstant x ξ t = failUnless $ isJust $ preview #_Constant t

pruneVar :: Prune es
pruneVar x ξ t = failUnless $ maybe False (`elem` ξ) $ preview #_Var t

pruneLam :: Prune es
pruneLam x ξ t = do
  ((bdr, typ), body) <- previewOrFail #_Lambda t
  prune x (ξ <> [bdr]) body

pruneForall :: Prune es
pruneForall x ξ t = do
  ((bdr, typ), body) <- previewOrFail #_Forall t
  prune x (ξ <> [bdr]) body

pruneApp :: Prune es
pruneApp x ξ t = do
  (f, args) <- fromJustOrFail $ extractApps t
  prune x ξ f
  forM_ args $ prune x ξ

lookupMetaDeclForMetaVar :: Binder -> MetaContext -> Maybe (MetaVariable, Term, LocalContext)
lookupMetaDeclForMetaVar d =
  find ((== d) . (^. _1)) . mapMaybe (preview #_MetaDecl) . getMetaContext

pruneMetaNoPrune :: Prune es
pruneMetaNoPrune x ξ t = do
  (y, σ) <- previewOrFail #_MetaVar t
  failUnless $ x /= y
  _Σ <- S.gets metaContext
  (_, τ, ψ₀) <- fromJustOrFail $ lookupMetaDeclForMetaVar y _Σ
  ψ₁ <- pruneContext ψ₀ x ξ σ
  failUnless $ ψ₀ == ψ₁

sanitize :: [Variable] -> LocalContext -> LocalContext
sanitize _ (LocalContext []) = LocalContext []
sanitize ξ (LocalContext (local : (LocalContext -> ψ))) =
  let
    (x, _T) = anyLocal local
    isSubsetOfξ = (`Set.isSubsetOf` Set.fromList ξ)
   in
    if isSubsetOfξ (freeVars _T)
      && maybe True (isSubsetOfξ . freeVars) (preview (#_LocalDef . _2) local)
      then
        let ψ' = sanitize (x : ξ) ψ
         in -- FIXME: This looks fishy, should it preseve local defs?  May be typo
            -- in paper.
            LocalContext [LocalDecl (x, _T)] <> ψ'
      else sanitize ξ ψ

-- Note: this will fail if/when we make Binder a newtype, in which case we'll
-- need a Binder to Variable helper.
varOfLocal :: Local -> Variable
varOfLocal (LocalDecl (b, _)) = b
varOfLocal (LocalDef (b, _, _)) = b

varsOfLocalContext :: LocalContext -> [Variable]
varsOfLocalContext (LocalContext locals) = map varOfLocal locals

pruneMeta :: Prune es
pruneMeta x ξ t = do
  (y, σ) <- previewOrFail #_MetaVar t
  failUnless $ x /= y
  _Σ <- metaContext <$> S.get
  (_, τ, ψ₀) <- fromJustOrFail $ lookupMetaDeclForMetaVar y _Σ
  ψ₁ <- pruneContext ψ₀ x ξ σ
  let ψ₂ = sanitize [] ψ₁
  prune x (varsOfLocalContext ψ₂) τ
  failUnless $ ψ₀ == ψ₁

pattern EmptyLocalContext :: LocalContext
pattern EmptyLocalContext = LocalContext []

pattern ConsLocalContext :: Local -> [Local] -> LocalContext
pattern ConsLocalContext local locals = LocalContext (local : locals)

-- | Extract the common data of all locals, regardless of decl/def.
anyLocal :: Local -> (Binder, Typ)
anyLocal (LocalDecl bt) = bt
anyLocal (LocalDef (b, _, t)) = (b, t)

-- TODO: Consider turning ξ into a set before calling pruneContext
pruneContext :: PruneContext es
pruneContext EmptyLocalContext _ _ _ = return EmptyLocalContext
-- Ambiguous in paper: likely we also prune local defs
pruneContext (ConsLocalContext local (LocalContext -> locals)) x ξ (unsnoc -> Just (σ, t)) = do
  let (z, _A) = anyLocal local
  locals' <- pruneContext locals x ξ σ
  return $
    if freeVars t `Set.isSubsetOf` Set.fromList ξ
      && x `notElem` freeMetaVars t
      then locals' <> LocalContext [LocalDecl (z, _A)]
      else do locals'

isStuck ::
  ND.NonDet :> es =>
  UnifierEffects es =>
  Term ->
  Eff es Bool
isStuck t = do
  t' <- weakHeadExpand t
  t'' <- weakHeadBetaZetaIotaTheta t'
  case t'' of
    Var _ -> return True

consDeltaNotStuckR :: Unifier es
consDeltaNotStuckR t u = do
  failIf =<< isStuck u
  u' <- weakHeadExpand u
  unify t u'

consDeltaStuckL :: Unifier es
consDeltaStuckL t u = do
  failUnless =<< isStuck u
  t' <- weakHeadExpand t
  unify t' u

consDeltaR :: Unifier es
consDeltaR t u = do
  u' <- weakHeadExpand u
  unify t u'

consDeltaL :: Unifier es
consDeltaL t u = do
  t' <- weakHeadExpand t
  unify t' u

freshMetaVar :: Eff es MetaVariable
freshMetaVar = return "FRESH"

ensureProduct ::
  ND.NonDet :> es =>
  UnifierEffects es =>
  Typ ->
  Term ->
  Eff es ()
ensureProduct _T _U = do
  _Σ₀ <- S.gets metaContext
  _Γ <- R.asks localContext
  v <- freshMetaVar
  let _Σ₁ = _Σ₀ <> MetaContext [MetaDecl v TypeOfTypes (_Γ <> LocalContext [LocalDecl ("y", _T)])]
  S.modify @State (set #metaContext _Σ₁)
  -- the paper doesn't really type-check here...
  convertible _U (Forall ("y", _T) (MetaVar v (map Var (typeErase _Γ) <> [Var "y"])))

typeOf :: Term -> Eff es Typ
typeOf = error "TODO"

lamEtaR :: Unifier es
lamEtaR u (preview #_Lambda -> Just ((x, _T), t)) = do
  failIf . isJust . preview #_Lambda $ u
  _U <- typeOf u
  ensureProduct _T _U
  R.local @Reader (over #localContext (<> LocalContext [LocalDecl (x, _T)])) $
    convertible (App u (Var x)) t
lamEtaR _ _ = ND.emptyEff

lamEtaL :: Unifier es
lamEtaL (preview #_Lambda -> Just ((x, _T), t)) u = do
  failIf . isJust . preview #_Lambda $ u
  _U <- typeOf u
  ensureProduct _T _U
  R.local @Reader (over #localContext (<> LocalContext [LocalDecl (x, _T)])) $
    convertible (App u (Var x)) t
lamEtaL _ _ = ND.emptyEff

-- c.f. Section 4.5
unify :: Unifier es
unify t u =
  let tryTactic tac = tac t u
   in ND.sumEff
        ( tryTactic
            <$> [ metaDeltaR
                , metaDeltaL
                , metaSameSame -- note: no need for metaSame if no universes
                , metaInstR
                , metaFirstOrderR
                , metaReducer
                , -- more stuff
                  lamBetaR
                , letZetaR
                , lamBetaL
                , letZetaL
                , consDeltaNotStuckR
                , consDeltaStuckL
                , consDeltaR
                , consDeltaL
                , lamEtaR
                , lamEtaL
                ]
        )

runUnifier :: Term -> Term -> IO (Either ND.CallStack (), State)
runUnifier t u =
  runEff
    . R.runReader (Reader (LocalContext []))
    . S.runState (State (MetaContext []))
    . ND.runNonDet ND.OnEmptyRollback
    $ unify t u
