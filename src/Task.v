Require Import Data.Maybe.

(* The Task abstraction *)
Record Task (C : (Type -> Type) -> Type) (K V : Type) :=
  mkTask {run : forall F `{C F}, ((K -> F V) -> F V)}.

Definition Tasks (C : (Type -> Type) -> Type) (K V : Type) :=
  K -> Maybe (Task C K V).
