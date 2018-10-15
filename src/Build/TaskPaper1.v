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
Local Open Scope string_scope.

Definition natPlus n m := n + m.

Definition natMul n m := n * m.

Inductive Task (C : (Type -> Type) -> Type) (K : Type) (V : Type) := {
  run : forall {F} `{CF: C F}, K -> Maybe ((K -> F V) -> F V)}.

Definition Task' (C : (Type -> Type) -> Type) (K : Type) (V : Type) :=
  forall {F} `{CF: C F}, K -> Maybe ((K -> F V) -> F V).

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

Module T.

Variable K V : Type.
Variable C : (Type -> Type) -> Type.
Variable F : (Type -> Type).
Variable task : Task Applicative K V.

Check run task (C:=Applicative) (F:=F).

End T.

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
