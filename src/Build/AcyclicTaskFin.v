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

Definition TotalTasks (C : (Type -> Type) -> Type) (V : Type) :=
  forall (k : nat), Maybe (Task C (Fin.t k) V).

(* Definition depth {C : (Type -> Type) -> Type} {V : Type} {F : (Type -> Type)} `{CF: C F} *)
(*            (tasks : TotalTasks C V) (key : nat) : nat := *)
(*   match tasks key with *)
(*   | Nothing => 0 *)
(*   | Just _  => key *)
(*   end. *)

Open Scope monad_scope.

(* (* TODO: use standart lemmas instead of these ad-hoc ones *) *)
(* Lemma succ_gt_zero : forall n, 0 = S n -> False. *)
(* Proof. intros. omega. Qed. *)

(* Lemma succ_eq_impls_eq : forall n m, S n = S m -> n = m. *)
(* Proof. intros. omega. Qed. *)

(* Lemma succsucc_gt_zero : forall n, 0 = S (S n) -> False. *)
(* Proof. intros. omega. Qed. *)

(* (* Safely convert a (p : nat) into a Fin.t n if n = S p *) *)
(* Fixpoint of_nat_succ {p n : nat} : n = S p -> t n := *)
(*   match n with *)
(*     |0 => fun H : 0 = S p => False_rect _ (succ_gt_zero p H) *)
(*     |S n' => match p with *)
(*       |0 => fun _ => @F1 n' *)
(*       |S p' => fun H => FS (of_nat_succ (succ_eq_impls_eq _ _ H)) *)
(*     end *)
(*   end. *)

(* (* Safely convert a (p : nat) into a Fin.t n if n = S (S p) *) *)
(* (* TODO: reuse of_nat_succ *) *)
(* Fixpoint of_nat_succsucc {p n : nat} : n = S (S p) -> t n := *)
(*   match n with *)
(*     |0 => fun H : 0 = S (S p) => False_rect _ (succsucc_gt_zero p H) *)
(*     |S n' => match p with *)
(*       |0 => fun _ => @F1 n' *)
(*       |S p' => fun H => FS (of_nat_succsucc (succ_eq_impls_eq _ _ H)) *)
(*     end *)
(*   end. *)

(* (* Can't come up with a short name for this lemma, so let is just be l *) *)
(* Lemma l : forall {n n' n''}, *)
(*     n = S n' -> n' = S n'' -> n = S (S n''). *)
(* Proof. intros. omega. Qed. *)

(* Fixpoint from_nat (p : nat) : Fin.t (S p) := *)
(*   match p with *)
(*   |0 => F1 *)
(*   |S p' => FS (from_nat p') *)
(*   end. *)

(* Fixpoint inject__1 {m} (x : Fin.t m) : Fin.t (S m) := *)
(*   match x with *)
(*   | F1 => F1 *)
(*   | FS x' => FS (inject__1 x') *)
(*   end. *)

(* Check Fin.L. *)
(* Print Fin.L. *)

(* Definition fibonacci : *)
(*   TotalTasks Applicative nat := fun n => *)
(*   match n with *)
(*   | 0  => Nothing *)
(*   | 1  => Nothing *)
(*   | S (S m) => Just *)
(*       {| run := fun _ _ => fun fetch => *)
(*            Nat.add <$> fetch (from_nat (S m)) *)
(*                    <*> fetch (inject__1 (from_nat m)) |} *)
(*   end. *)

(* Definition dependencies {K V : Type} (task : Task Applicative K V) : list K := *)
(*   getConst ((run task) (fun k => mkConst (cons k nil))). *)

(* Definition deps_fib (k : nat) : list nat := *)
(*   match fibonacci k with *)
(*   | Nothing => nil *)
(*   | Just task => map (fun x => proj1_sig (Fin.to_nat x)) (dependencies task) *)
(*   end. *)

(* Eval compute in deps_fib (S (S 1)). *)

(**********************************************************************)

Program Fixpoint busyFetch
  (tasks : TotalTasks Monad nat) (k : nat) {measure k}:
  (State (Store unit nat nat) nat) :=
  match tasks k with
  | Nothing   => gets (getValue k)
  | Just task =>
      (run (F:=State (Store unit nat nat)) task) (fun n => busyFetch tasks (proj1_sig (Fin.to_nat n)))
      (* (run task) (fun n => busyFetch tasks (proj1_sig (Fin.to_nat n))) *)
      >>=
      (fun v => modify (putValue k v) >> pure v)
  end.
