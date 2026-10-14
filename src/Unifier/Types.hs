{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module Unifier.Types where

import Control.Lens ()
import Control.Monad (unless)
import Data.Generics.Labels ()
import Data.Maybe (fromJust, fromMaybe, isJust)
import Data.Monoid (First)
import Data.Set qualified as Set
import Effectful (Eff, IOE, MonadIO (liftIO), runEff, (:>))
import Effectful.NonDet (runNonDet)
import Effectful.NonDet qualified as ND
import Effectful.Reader.Static qualified as R
import Effectful.State.Static.Local qualified as S
import GHC.Generics (Generic)
import Prettyprinter qualified as PP

type Binder = String
type Constant = String
type MetaVariable = String
type SuspendedSubstitution = [Term]
type Typ = Term
type Variable = String

class TypeErase t a | t -> a where
  typeErase :: t -> a

instance TypeErase Local Binder where
  typeErase (LocalDecl (b, _)) = b
  typeErase (LocalDef (b, _, _)) = b

data Local
  = LocalDecl (Binder, Typ)
  | LocalDef (Binder, Term, Typ)
  deriving (Eq, Generic)

localBinder :: Local -> Binder
localBinder = typeErase

localType :: Local -> Typ
localType (LocalDecl (_, τ)) = τ
localType (LocalDef (_, _, τ)) = τ

newtype LocalContext = LocalContext {getLocalContext :: [Local]}
  deriving (Eq, Semigroup)

instance TypeErase LocalContext [Binder] where
  typeErase (LocalContext locals) = map typeErase locals

instance PP.Pretty LocalContext where
  pretty (LocalContext γ) = "TODO"

data Meta
  = MetaDecl MetaVariable Typ LocalContext
  | MetaDef MetaVariable Term Typ LocalContext
  deriving (Generic)

newtype MetaContext = MetaContext {getMetaContext :: [Meta]}
  deriving (Semigroup)

instance PP.Pretty MetaContext where
  pretty (MetaContext e) = "TODO"

-- WARNING: The `Eq` instance is syntactic equality!!!  Not even
-- alpha-equivalence!!!
data Term
  = App Term Term
  | Constant Constant
  | Forall (Binder, Typ) Typ
  | Lambda (Binder, Typ) Term
  | Let (Binder, Term, Typ) Term
  | MetaVar MetaVariable SuspendedSubstitution
  | Var Variable
  | TypeOfTypes
  deriving (Eq, Generic)

instance PP.Pretty Term where
  pretty (App f arg) = "(" <> PP.pretty f <> " " <> PP.pretty arg <> ")"
  pretty (Constant c) = PP.pretty c
  pretty (Var v) = PP.pretty v

instance Show Term where
  show = show . PP.pretty

newtype Reader = Reader
  { localContext :: LocalContext
  }
  deriving (Generic)

newtype State = State
  { metaContext :: MetaContext
  }
  deriving (Generic)

type UnifierEffects es =
  ( IOE :> es
  , R.Reader Reader :> es
  , S.State State :> es
  )

type Prune es =
  ND.NonDet :> es =>
  UnifierEffects es =>
  MetaVariable ->
  [Variable] ->
  Term ->
  Eff es ()

type PruneContext es =
  ND.NonDet :> es =>
  UnifierEffects es =>
  LocalContext ->
  MetaVariable ->
  [Variable] ->
  SuspendedSubstitution ->
  Eff es LocalContext

type Reducer es =
  ND.NonDet :> es =>
  UnifierEffects es =>
  Term ->
  Eff es Term

type Unifier es =
  ND.NonDet :> es =>
  UnifierEffects es =>
  Term ->
  Term ->
  Eff es ()
