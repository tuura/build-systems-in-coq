Require Import Build.Task.
Require Import Build.Store.

(* Record Task (C : (Type -> Type) -> Type) (K V : Type) := *)
(*   mkTask {run : forall F `{C F}, ((K -> F V) -> F V)}. *)

(* Definition Tasks (C : (Type -> Type) -> Type) (K V : Type) := *)
(*   K -> Maybe (Task C K V). *)

Definition Build (C : (Type -> Type) -> Type) (I K V : Type) :=
  Tasks C K V -> K -> Store I K V -> Store I K V.