Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.
Require Import Data.Maybe.
Require Import Data.Functor.
Require Import Data.Functor.Const.
Require Import Control.Applicative.
Require Import Control.Monad.
Require Import Control.Monad.State.
Require Import Build.Store.
Require Import Prelude.
Require Import Coq.Program.Wf.
Require Import Omega.
Require Import Strings.String.
Local Open Scope string_scope.
Require Import ssreflect.

Definition natPlus n m := n + m.

Definition natMul n m := n * m.

Inductive Task (C : (Type -> Type) -> Type) (K V : Type) := {
  run : forall {F} `{CF: C F}, ((K -> F V) -> F V)}.

(* Declare the types of the constraint, key and value to be implicit *)
Arguments run {C} {K} {V} _ {F} {CF}.

Definition Tasks (C : (Type -> Type) -> Type) (K V : Type) :=
  K -> Maybe (Task C K V).

Definition depth {C : (Type -> Type) -> Type} {F : (Type -> Type)} `{CF: C F}
           (key : nat) (tasks : Tasks C nat nat) : nat :=
  match tasks key with
  | Nothing => 0
  | Just _  => key
  end.

Open Scope monad_scope.

Definition fibonacci :
  Tasks Applicative nat nat := fun n =>
  match n with
  | 0  => Nothing
  | 1  => Nothing
  | S (S m) => Just
      {| run := fun _ _ => fun fetch =>
           Nat.add <$> fetch (S m)
                   <*> fetch m |}
  end.

Definition dependencies {K V : Type} (task : Task Applicative K V) : list K :=
  getConst ((run task) (fun k => mkConst (cons k nil))).

Definition deps_fib (k : nat) : list nat :=
  match fibonacci k with
  | Nothing => nil
  | Just task => dependencies task
  end.

Theorem deps_fib_correct : forall n, deps_fib (S (S n)) = (S n :: n :: nil).
Proof.
  reflexivity.
Qed.

Theorem deps_fib_correct' : forall n, dependencies (fibonacci (S (S n))) = (S n :: n :: nil).
Proof.
  reflexivity.
Qed.

Definition sprsh1 (key : string) : Task Applicative string nat :=
  match key with
  | "B1" => {| key   := key;
               fetch := fun _ _ =>
                 Just (fun fetch => natPlus <$> fetch "A1" <*> fetch "A2") |}
  | "B2" => {| key := key;
               fetch := fun _ _ =>
                 Just (fun fetch => natMul <$> fetch "B1" <*> pure 2) |}
  |  _   => {| key := key;
               fetch := fun _ _  => Nothing |}
  end.
