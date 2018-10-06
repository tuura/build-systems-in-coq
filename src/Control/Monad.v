Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Coq.Program.Basics.

Generalizable All Variables.

Class Monad (m : Type -> Type) := {
  is_applicative :> Applicative m;

  join : forall {a : Type}, m (m a) -> m a
}.

Arguments join {m _ _} _.

Definition bind `{Monad m} {X Y : Type} (f : (X -> m Y)) : m X -> m Y :=
  compose join (fmap f).

Delimit Scope monad_scope with monad.

Notation "join[ M ]" := (@join M _ _) (at level 9) : monad_scope.
Notation "join[ M N ]" := (@join (compose M N) _ _) (at level 9) : monad_scope.

Notation "m >>= f" := (bind f m) (at level 42, right associativity) : monad_scope.
Notation "a >> b" := (a >>= fun _ => b)%monad (at level 81, right associativity) : monad_scope.

Bind Scope monad_scope with Monad.