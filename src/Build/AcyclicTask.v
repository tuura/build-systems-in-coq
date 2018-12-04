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

Definition natPlus n m := n + m.

Definition natMul n m := n * m.

Inductive Task (C : (Type -> Type) -> Type) (K V : Type) := {
  run : forall {F} `{CF: C F}, (K -> F V) -> F V}.

(* Declare the types of the constraint, key and value to be implicit *)
Arguments run {C} {K} {V} _ {F} {CF}.

Definition AcyclicTasks (C : (Type -> Type) -> Type) (V : Type) :=
  forall (k : nat), Maybe (Task C {x:nat | k>x} V).

Definition depth {C : (Type -> Type) -> Type} {V : Type} {F : (Type -> Type)} `{CF: C F}
           (tasks : AcyclicTasks C V) (key : nat) : nat :=
  match tasks key with
  | Nothing => 0
  | Just _  => key
  end.

Require Import Coq.Init.Specif.

Lemma ok_k' (k:nat) : S k > k.
Proof. auto. Qed.

Definition ok_k (k : nat) := exist (gt (S k)) k (ok_k' k).

Lemma ok_kk' (k:nat) : S (S k) > k.
Proof. auto. Qed.

Definition ok_kk (k : nat) := exist (gt (S (S k))) k (ok_kk' k).

Definition fibonacci :
  AcyclicTasks Applicative nat := fun n =>
  match n with
  | 0  => Nothing
  | 1  => Nothing
  | S (S m) => Just
      {| run := fun _ _ => fun fetch => 
           Nat.add <$> fetch (ok_k (S m))
                   <*> fetch (ok_kk (m)) |}
  end.

(* -- | Find the dependencies of an applicative task. *)
(* dependencies :: Task Applicative k v -> [k] *)
(* dependencies task = getConst $ run task (\k -> Const [k]) *)

Definition dependencies {K V : Type} (task : Task Applicative K V) : list K :=
  getConst ((run task) (fun k => mkConst (cons k nil))).

(* Definition deps_fib (k : nat) : list (Fin.t k) := *)
(*   match fibonacci k with *)
(*   | Nothing => nil *)
(*   | Just task => dependencies task *)
(*   end. *)

Definition deps_fib (k : nat) : list nat :=
  match fibonacci k with
  | Nothing => nil
  | Just task => map (fun x => proj1_sig x) (dependencies task)
  end.

Eval compute in deps_fib (4).

(* dependencies (fib (S (S n)) == [n, S n] *)
