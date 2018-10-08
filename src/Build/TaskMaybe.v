Require Import Coq.Vectors.Fin.
Require Import Data.Maybe.
Require Import Data.Functor.
Require Import Data.Proxy.
Require Import Control.Applicative.
Require Import Control.Monad.
Require Import Control.Monad.State.
Require Import Build.Store.

Require Import Coq.Program.Wf.
(* Require Import Recdef. *)

Definition undefined {a : Type} : a. Admitted.

Definition const {A B : Type} (x : A) (y : B) : A := x.

Fixpoint eq_nat_impl n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat_impl n1 m1
  end.

Instance eq_nat : Eq nat := { eqb := eq_nat_impl}.

Definition ST v := State (Store unit nat v) v.

(* Definition Task (C : (Type -> Type) -> Type) := *)
(*   forall F `{C F}, (nat -> F nat) -> nat -> Maybe (F nat). *)

Definition Task :=
  (nat -> (State (Store unit nat nat) nat)) -> nat -> Maybe (State (Store unit nat nat) nat).

Definition depth (task : Task) (k : nat) : nat :=
  match (task (fun x => pure 0) k) with
  | Nothing => 0
  | Just k' => k'
  end.

(* Definition lengthOrder (ls1 ls2 : list A) := *)
(*   length ls1 < length ls2. *)

Open Scope monad_scope.

Definition natPlus n m := n + m.

Fixpoint fib (fetch : nat -> (State (Store unit nat nat) nat)) (n : nat) :
  Maybe (State (Store unit nat nat) nat)  :=
  match n with
  | O    => Nothing
  | S n' =>
    match n' with
    | O     => Nothing
    | S n'' => Just (natPlus <$> (fetch n'') <*> (fetch n'))
    end
  end.

Program Fixpoint busyFetch (task : Task Monad) (k : nat) :
  (State (Store unit nat nat) nat) :=
    (* let t := (run task) (fun k' => busyFetch task k') k in *)
    match task (busyFetch task) k  with
    | Nothing  => gets (getValue k)
    | Just act =>
      act >>=
          fun v => modify (putValue k v) >> pure v
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