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

Definition natPlus n m := n + m.

(* type Task2 c k v = forall f. c f => k -> Maybe ((k -> f v) -> f v) *)

(* Definition Task {C : (Type -> Type) -> Type} := forall F `{C F}, *)
(*   nat -> Maybe ((nat -> F nat) -> F nat). *)

Record Task :=
  { run: 
    nat -> Maybe ((nat -> State (Store unit nat nat) nat) -> State (Store unit nat nat) nat)   }.

Definition depth (task : Task) (k : nat) : nat :=
  match ((run task) k) with
  | Nothing => 0
  | Just _  => k
  end.

Open Scope monad_scope.

Lemma depth_of_nothing_is_zero : forall task k, (run task) k = Nothing -> depth task k = 0.
Proof.
  intros.
  unfold depth.
  rewrite H.
  reflexivity.
Qed.

Lemma depth_of_just_is_positive : forall task k f,
    k > 0 -> (run task) k = Just f -> depth task k > 0.
Proof.
  intros.
  unfold depth.
  rewrite H0.
  apply H.
Qed.

Lemma ttt : forall task, depth task 0 = 0.
Proof.
  intros.
  unfold depth.
  destruct (run task 0); reflexivity.
Qed.

Lemma just_is_deeper_that_nothing : forall task1 task2 k1 k2 f,
    (k2 > 0) ->
    (run task1) k1 = Nothing -> (run task2) k2 = Just f ->
    depth task1 k1 < depth task2 k2.
Proof.
  intros task1 task2 k1 k2 f Hk2positive task1Nothing task2Just.
  unfold depth.
  rewrite task1Nothing.
  rewrite task2Just.
  apply Hk2positive.
Qed.

Lemma lemma0 : forall n m, 

Lemma lemma1 : forall k1 k2, k1 > k2 -> k1 > 0.
Proof.
  intros.
  induction k2.
  induction k1.

Lemma t: forall task k1 k2, k1 < k2 -> depth task k1 <= depth task k2.
Proof.
  intros.  
  unfold depth.
    
  
  
  

(* Lemma t : forall task, forall k1 k2, k1 < k2 -> depth task k1 < depth task k2. *)
(* Proof. *)
(*   intros. *)
  

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

(* Fixpoint fib (n : nat) (fetch : nat -> (State (Store unit nat nat) nat)) : *)
(*   Maybe (State (Store unit nat nat) nat)  := *)
(*   match n with *)
(*   | O    => Nothing *)
(*   | S n' => *)
(*     match n' with *)
(*     | O     => Nothing *)
(*     | S n'' => Just (natPlus <$> (fetch n'') <*> (fetch n')) *)
(*     end *)
(*   end. *)

Fixpoint fib (n : nat) :
  Task :=
  match n with
  | O    => {| run := fun k => Nothing |}
  | S n' =>
    match n' with
    | O     => {| run := fun k => Nothing |}
    | S n'' =>
      {| run := fun k => Just (fun fetch => natPlus <$> (fetch n'') <*> (fetch n')) |}
    end
  end.

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
