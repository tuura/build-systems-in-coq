Require Import Coq.Vectors.Fin.
Require Import Data.Maybe.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Monad.
Require Import Control.Monad.State.
Require Import Build.Store.
Require Import Prelude.
Require Coq.Program.Wf.

Definition natPlus n m := n + m.

(* type Task2 c k v = forall f. c f => k -> Maybe ((k -> f v) -> f v) *)

(* Definition Task {C : (Type -> Type) -> Type} := forall F `{C F}, *)
(*   nat -> Maybe ((nat -> F nat) -> F nat). *)

Definition Task :=
  nat -> Maybe ((nat -> State (Store unit nat nat) nat) -> State (Store unit nat nat) nat).  
Definition depth (task : Task) (k : nat) : nat :=
  match (task k) with
  | Nothing => 0
  | Just _  => k
  end.

Definition taskOrder (task1 task2 : Task) :=
  forall k, depth task1 k < depth task2 k.

Open Scope monad_scope.

Lemma t : forall task, forall k1 k2, k1 < k2 -> depth task k1 < depth task k2.
Admitted.

(* Definition fib : Task := *)
(*   fun (n : nat) (fetch : nat -> (State (Store unit nat nat) nat)) (n : nat) => *)
(*     match n with  *)
(*     | O    => Nothing *)
(*     | S n' => *)
(*       match n' with *)
(*       | O     => Nothing *)
(*       | S n'' => Just (natPlus <$> (fetch n'') <*> (fetch n')) *)
(*       end *)
(*     end. *)

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

Program Fixpoint busyFetch (task : Task) (k : nat) {measure (depth task k)}:
  (State (Store unit nat nat) nat) :=
    (* let t := (run task) (fun k' => busyFetch task k') k in *)
    match task k  with
    | Nothing  => gets (getValue k)
    | Just act => undefined
    end.

Check busyFetch (Task fib).

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
