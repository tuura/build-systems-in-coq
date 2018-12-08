(* The identity functor, applicative and monad. *)

Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Monad.

Inductive Identity A := mkIdentity {runIdentity : A}.

Arguments mkIdentity {_} _.
Arguments runIdentity {_} _.

Instance Identiry_Functor : Functor Identity :=
  {
    fmap {_} {_} f x := mkIdentity (f (runIdentity x))
  }.

Instance Identity_Applicative : Applicative Identity :=
  {
    pure _ x := mkIdentity x;
    ap _ _ f x := mkIdentity ((runIdentity f) (runIdentity x))
  }.

Instance Identity_Monad : Monad Identity := {
  join _ x := runIdentity x
}.
