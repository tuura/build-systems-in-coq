Require Import Data.Functor.

Generalizable All Variables.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (f : Type -> Type) := {
  is_functor :> Functor f;

  pure : forall a : Type, a -> f a;
  ap   : forall a b : Type, f (a -> b) -> f a -> f b
    where "f <*> g" := (ap f g)
                                       }.

Arguments pure {f _ _} _.
Arguments ap   {f _ _ _} _ x.

Infix "<*>" := ap (at level 28, left associativity).