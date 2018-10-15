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
Require Import Strings.String.
From mathcomp.ssreflect Require Import ssreflect.
Require Fin.

Local Open Scope string_scope.
Require Import Coq.Init.Specif.

Definition natPlus n m := n + m.

Definition natMul n m := n * m.

Definition undefined {a : Type} : a. Admitted.

Fixpoint eq_nat_impl n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat_impl n1 m1
  end.

Instance eq_nat : Eq nat := { eqb := eq_nat_impl}.

Record Task (C : (Type -> Type) -> Type) := {
  key : nat;
  run : forall {F} `{CF: C F}, nat -> Maybe ((t key -> F nat) -> F nat)}.

(* Declare the types of the constraint, key and value to be implicit *)
Arguments run {C} _ {F} {CF} _.
Arguments key {C} _.

Definition depth {C : (Type -> Type) -> Type} {F : (Type -> Type)} `{CF: C F}
           (task : Task C) (k : nat) : nat :=
  match ((run (F:=F) (CF:=CF) task) k) with
  | Nothing => 0
  | Just _  => k
  end.

Open Scope monad_scope.

Module T.

Variable K V : Type.
Variable C : (Type -> Type) -> Type.
Variable F : (Type -> Type).
Variable task : Task Applicative.

Check run task (C:=Applicative) (F:=F).

End T.

Theorem t1 : forall k, k < S k.
Proof. move=>k. done. Qed.

Theorem t2 : forall k, k < S (S k).
Proof. move=>k. omega. Qed.

Theorem two_gt0 : 2 > 0.
Proof. omega. Qed.

Theorem t3 {C : (Type -> Type) -> Type}:
  forall (task : Task C) (n : nat), key task = (S n) -> n < key task.
Proof.
  move=>task n H.
  omega.
Qed.


Check two_gt0.

Check exist _ 2 two_gt0.

Lemma ltnSn n m : (S n = m) -> n < m.
Proof. intros. omega. Qed.

Fixpoint fibonacci (n : nat) :
  Task Applicative :=
  match n with
  | O    => {| key := 1; run := fun _ _ _ => Nothing |}
  | S n' =>
    match n' with
    | O     => {| key := 1; run := fun _ _ _ => Nothing |}
    | S n'' => {| key := n;
                  run := fun _ _ k =>
                  let x := of_nat n' n in
                  match x with
                  | inleft x' => Just (fun fetch => natPlus  <$>
                                                    fetch x' <*>
                                                    pure 2)
                  | inright prf => Nothing
                  end |}
    end
  end.

Fixpoint fibonacci' (n : nat) :
  Task Applicative :=
  match n with
  | O    => {| key := 1; run := fun _ _ _ => Nothing |}
  | S n' =>
    match n' with
    | O     => {| key := 1; run := fun _ _ _ => Nothing |}
    | S n'' => {| key := n;
                  run := fun _ _ k =>
                  let x := @of_nat_lt n'' n undefined in
                  let y := @of_nat_lt n'  n undefined in
                  Just (fun fetch => natPlus  <$> fetch x <*>
                                                  fetch y)
               |}
    end
  end.

Fixpoint busyFetch (task : Task Monad) (k : nat):
  (State (Store unit nat nat) nat) :=
    (* let t := (run task) (fun k' => busyFetch task k') k in *)
    match (run task) k  with
    | Nothing  => gets (getValue k)
    | Just act =>
      (act (fun x => busyFetch task k)) >>=
          fun v => modify (putValue k v) >> pure v
    end.

Fixpoint fibonacci' (n : nat) :
  Task' Applicative nat nat :=
  match n with
  | O    => fun {F} {CF} k => Nothing
  | S n' =>
    match n' with
    | O     => fun {F} {CF} k => Nothing
    | S n'' => fun {F} {CF} k =>
                  Just (fun fetch => natPlus <$> (fetch n'') <*> (fetch n'))
    end
  end.

Definition sprsh1 (key : string) : Task Applicative string nat :=
  match key with
  | "B1" => {| run := fun _ _ _ =>
                 Just (fun fetch => natPlus <$> fetch "A1" <*> fetch "A2") |}
  | "B2" => {| run := fun _ _ _ =>
                 Just (fun fetch => natMul <$> fetch "B1" <*> pure 2) |}
  |  _   => {| run := fun _ _ _  => Nothing |}
  end.

(****************************************************************************)

(* adaptRebuilder :: Rebuilder Monad i k v -> Rebuilder Applicative i k v *)
(* adaptRebuilder rebuilder key value task = rebuilder key value $ Task $ run task *)

Definition adapt {K V : Type} (task : Task Applicative K V) : Task Monad K V :=
  let r := run task (C:=Applicative)
  in {| run := fun _ _ => r |}.

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
