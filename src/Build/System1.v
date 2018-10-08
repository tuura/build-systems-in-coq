Require Import Coq.Vectors.Fin.
Require Import Data.Maybe.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Monad.
Require Import Control.Monad.State.
Require Import Build.Store.

Require Import Coq.Program.Wf.
(* Require Import Recdef. *)

Definition undefined {a : Type} : a. Admitted.

(* (* The Task abstraction *) *)
(* Record Task (C : (Type -> Type) -> Type) (K V : Type) := *)
(*   mkTask {key : K; run : forall F `{C F}, ((K -> F V) -> F V)}. *)

(* Record Task1 (V : Type) := *)
(*   mkTask1 { key1 : nat *)
(*           ; run1 : forall F `{Monad F}, (nat -> F V) -> nat -> Maybe (F V)}. *)

(* Record Task := *)
(*   mkTask { key : nat *)
(*          ; run : forall F `{Monad F}, (forall k : nat, k < key -> F unit) -> *)
(*                                        nat -> *)
(*                                        Maybe (F unit)}. *)

Fixpoint eq_nat_impl n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat_impl n1 m1
  end.

Instance eq_nat : Eq nat := { eqb := eq_nat_impl}.

Definition ST := State (Store unit nat nat) nat.

(* Record Task := *)
(*   mkTask { key : nat *)
(*          ; run  : (nat -> ST) -> nat -> ST}. *)

Definition Task := (nat -> ST) -> nat -> ST.

Open Scope monad_scope.

(* Program Fixpoint busyFetch (task : Task) (k : nat) *)
(*   {measure (depth task)}: *)
(*   ST unit := *)
(*     let t := (run task) (fun k' => busyFetch task k') k in *)
(*     match t with *)
(*     | Nothing  => gets (getValue k) *)
(*     | Just act => *)
(*       act >>= *)
(*           fun v => modify (putValue k v) >> pure v *)
(*     end. *)

Definition natPlus n m := n + m.

Fixpoint fib (n : nat) : nat :=
  match n with
  | O    => 1
  | S n' =>
    match n' with
    | O    => 1
    | S n'' => (fib n'') + (fib n')
    end
  end.

Fixpoint busyFib (n : nat) : ST :=
  match n with
  | O    =>  gets (getValue 0)
  | S n' =>
    match n' with
    | O    =>  gets (getValue 1)
    | S n'' => natPlus <$> busyFib n'' <*> busyFib n' >>=
               fun v => modify (putValue n v) >> pure v
    end
  end.

Section TaskFib.

End TaskFib.