Require Import Coq.Vectors.Fin.
Require Import Data.Maybe.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Monad.
Require Import Control.Monad.State.
Require Import Build.Store.
Require Import Prelude.
Require Import Coq.Program.Wf.
Require Import Omega.

Fixpoint eq_nat_impl n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat_impl n1 m1
  end.

Instance eq_nat : Eq nat := { eqb := eq_nat_impl}.

Definition natPlus n m := n + m.

Record Task (C : (Type -> Type) -> Type) (K : Type) (V : Type) := {
  run : forall {F} `{CF: C F}, nat -> Maybe ((nat -> F nat) -> F nat)}.

Definition Task' (C : (Type -> Type) -> Type) (K : Type) (V : Type) :=
  forall {F} `{CF: C F}, nat -> Maybe ((nat -> F nat) -> F nat).

(* Declare the types of the constraint, key and value to be implicit *)
Arguments run {C} {K} {V} _ {F} {CF} _.

Definition depth {C : (Type -> Type) -> Type} {F : (Type -> Type)} `{CF: C F}
           (task : Task C nat nat) (k : nat) : nat :=
  match ((run (F:=F) (CF:=CF) task) k) with
  | Nothing => 0
  | Just _  => k
  end.

Open Scope monad_scope.

Fixpoint fibonacci (n : nat) :
  Task Applicative nat nat :=
  match n with
  | O    => {| run := fun {F} {CF} k => Nothing |}
  | S n' =>
    match n' with
    | O     => {| run := fun {F} {CF} k => Nothing |}
    | S n'' => {| run := fun {F} {CF} k =>
                  Just (fun fetch => natPlus <$> (fetch n'') <*> (fetch n')) |}
    end
  end.

Fixpoint fibonacci' (n : nat) :
  Task' Applicative nat nat :=
  match n with
  | O    => fun _ _ _  => Nothing
  | S n' =>
    match n' with
    | O     => fun _ _ _  => Nothing
    | S n'' => fun _ _ _ =>
                  Just (fun fetch => natPlus <$> (fetch n'') <*> (fetch n'))
    end
  end.

Fixpoint busyFetch (task : Task Monad nat nat) (k : nat):
  (State (Store unit nat nat) nat) :=
    match (run task) k  with
    | Nothing  => gets (getValue k)
    | Just act =>
      (act (fun x => busyFetch task k)) >>=
          fun v => modify (putValue k v) >> pure v
    end.

Fixpoint fibonatty' (n : nat) : Task' Monad nat nat :=
  fibonacci' n >>= fun fn =>
    if Nat.even n
    then fun {F} {CF} k => Just (fun fetch => pure fn)
    else fun {F} {CF} k => Just (fun fetch => pure n).

Program Fixpoint busyFetch (task : Task) (k : nat) {measure (depth task k)}:
  (State (Store unit nat nat) nat) :=
    (* let t := (run task) (fun k' => busyFetch task k') k in *)
    match (run task) k with
    | Nothing  => gets (getValue k)
    | Just act => undefined
    end.

Check busyFetch fib.

Program Fixpoint busyFetch (task : Task) (k : nat) {measure (depth task k)}:
  (State (Store unit nat nat) nat) :=
    (* let t := (run task) (fun k' => busyFetch task k') k in *)
    match task k  with
    | Nothing  => gets (getValue k)
    | Just act =>
      (act (fun x => busyFetch task k)) >>=
          fun v => modify (putValue k v) >> pure v
    end.

Fixpoint busyFib (n : nat) : State (Store unit nat nat) nat :=
  match n with
  | O    =>  gets (getValue 0)
  | S n' =>
    match n' with
    | O    =>  gets (getValue 1)
    | S n'' => natPlus <$> busyFib n'' <*> busyFib n' >>=
               fun v => modify (putValue n v) >> pure v
    end
  end.
