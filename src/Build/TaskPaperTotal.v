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

Inductive Task (C : (Type -> Type) -> Type) (K V : Type) := {
  run : forall {F} `{CF: C F}, (K -> F V) -> F V}.

(* Declare the types of the constraint, key and value to be implicit *)
Arguments run {C} {K} {V} _ {F} {CF}.

Definition TotalTasks (C : (Type -> Type) -> Type) :=
  forall (k : nat), Maybe (Task C (Fin.t k) nat).

Definition depth {C : (Type -> Type) -> Type} {F : (Type -> Type)} `{CF: C F}
           (tasks : TotalTasks C) (key : nat) : nat :=
  match tasks key with
  | Nothing => 0
  | Just _  => key
  end.

Open Scope monad_scope.

(* TODO: use standart lemmas instead of these ad-hoc ones *)
Lemma succ_gt_zero : forall n, 0 = S n -> False.
Proof. intros. omega. Qed.

Lemma succ_eq_impls_eq : forall n m, S n = S m -> n = m.
Proof. intros. omega. Qed.

Lemma succsucc_gt_zero : forall n, 0 = S (S n) -> False.
Proof. intros. omega. Qed.

(* Safely convert a (p : nat) into a Fin.t n if n = S p *)
Fixpoint of_nat_succ {p n : nat} : n = S p -> t n :=
  match n with
    |0 => fun H : 0 = S p => False_rect _ (succ_gt_zero p H)
    |S n' => match p with
      |0 => fun _ => @F1 n'
      |S p' => fun H => FS (of_nat_succ (succ_eq_impls_eq _ _ H))
    end
  end.

(* Safely convert a (p : nat) into a Fin.t n if n = S (S p) *)
(* TODO: reuse of_nat_succ *)
Fixpoint of_nat_succsucc {p n : nat} : n = S (S p) -> t n :=
  match n with
    |0 => fun H : 0 = S (S p) => False_rect _ (succsucc_gt_zero p H)
    |S n' => match p with
      |0 => fun _ => @F1 n'
      |S p' => fun H => FS (of_nat_succsucc (succ_eq_impls_eq _ _ H))
    end
  end.

(* Can't come up with a short name for this lemma, so let is just be l *)
Lemma l : forall {n n' n''},
    n = S n' -> n' = S n'' -> n = S (S n'').
Proof. intros. omega. Qed.

Fixpoint from_nat (p : nat) : Fin.t (S p) :=
  match p with
  |0 => F1
  |S p' => FS (from_nat p')
  end.

Fixpoint inject____1 {m} (x : Fin.t m) : Fin.t (S m) :=
  match x with
  | F1 => F1
  | FS x' => FS (inject____1 x')
  end.

Definition fibonacci :
  TotalTasks Applicative := fun n =>
  match n with
  | 0  => Nothing
  | 1  => Nothing
  | S (S m) => Just
      {| run := fun _ _ => fun fetch =>
           Nat.add <$> fetch (from_nat (S m))
                   <*> fetch (inject____1 (from_nat m)) |}
  end.

(* Note: of_nat_succ p1 can be expanded to @of_nat_succ n' n p1 to specify
   the implicit n' (the nat to convert) and n (the upper bound). It feels
   less obscure, but looks realy ugly *)
Definition fibonacci' :
  TotalTasks Applicative :=
  fun n =>
  (* Match on n and get proofs of equality in the branches (like p1 : S n' = n) *)
  match n as m return n = m -> Maybe (Task Applicative (Fin.t n) nat) with
  | O    => fun _ => Nothing
  | S n' => fun p1 =>
    match n' as m' return n' = m' -> Maybe (Task Applicative (Fin.t n) nat) with
    | O     => fun _  => Nothing
    | S n'' => fun p2 => Just
      {| run := fun _ _ =>
           (fun fetch => natPlus <$> fetch (of_nat_succ p1)
                                 <*> fetch (of_nat_succsucc (l p1 p2))) |}
    end eq_refl
  end eq_refl.

Fixpoint busyFetch (tasks : TotalTasks Monad) {n : nat} (k : Fin.t n):
  (State (Store unit (Fin.t n) nat) nat) :=
    (* let t := (run task) (fun k' => busyFetch task k') k in *)
    match tasks n with
    | Nothing  => gets (getValue k)
    | Just task => (run task) (busyFetch tasks) >>= fun v => undefined
    end.