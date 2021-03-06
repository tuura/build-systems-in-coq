Require Import Data.Maybe.
Require Import Data.Functor.
Require Import Data.Functor.Identity.
Require Import Control.Applicative.
Require Import Control.Monad.
Require Import Control.Monad.StateInductive.
Require Import Build.AcyclicTask.
Require Import Build.Store.

Require Import Coq.Program.Wf.

Open Scope monad_scope.

Definition undefined {a : Type} : a. Admitted.

(* -- | This is a correct but non-minimal build system: given a target key it *)
(* -- recursively rebuilds its dependencies, even if they are already up to date. *)
(* -- There is no memoisation, therefore the a key may be built multiple times. *)
(* busy :: forall k v. Eq k => Build Monad () k v *)
(* busy tasks key store = execState (fetch key) store *)
(*   where *)
(*     fetch :: k -> State (Store () k v) v *)
(*     fetch k = case tasks k of *)
(*         Nothing   -> gets (getValue k) *)
(*         Just task -> do v <- task fetch; modify (putValue k v); return v *)

(* Implementation of busyFetch by Alexandre Moine *)
(* Program Fixpoint requires the result to be wrapped in an inductive type. *)
Program Fixpoint busyFetch (V : Type) (tasks : AcyclicTasks Applicative V) (k:nat)
  {measure k}
  : (Maybe nat * State (Store unit nat V) V) :=
  match tasks k with
  | Nothing   => (Nothing,gets (getValue k))
  | Just task => (Just k,
    (run task)
    (fun n => snd (busyFetch V tasks (proj1_sig n)))
    >>=
    (fun v => modify (putValue k v) >> pure v))
  end.

(* Looks like even the Identity type is good enough for Coq *)
Program Fixpoint busyFetch' (V : Type) (tasks : AcyclicTasks Applicative V) (k:nat)
  {measure k}
  : Identity (State (Store unit nat V) V) :=
  match tasks k with
  | Nothing   => Id _ (gets (getValue k))
  | Just task => Id _ (
    (run task)
    (fun n => getIdentity (busyFetch' V tasks (proj1_sig n)))
    >>=
    (fun v => modify (putValue k v) >> pure v))
  end.

(* But for some reason, Coq can't handle the unwrapped constructor. *)
Program Fixpoint busyFetch'' (tasks : AcyclicTasks Applicative nat) (k:nat)
  {measure k}
  : (State (Store unit nat nat) nat) :=
  match tasks k with
  | Nothing   => gets (getValue k)
  | Just task =>
    (run task)
    (fun n => busyFetch'' tasks (proj1_sig n))
    >>=
    (fun v => modify (putValue k v) >> pure v)
  end.

Definition busy (V : Type) (tasks : AcyclicTasks Applicative V) (key : nat)
  (store : Store unit nat V) : Store unit nat V :=
  snd ((snd (busyFetch V tasks key)) store).

(* Fibonacci *)

Definition store_fibo (zero : nat) (one : nat) :=
  mkStore unit nat nat tt (fun k => if Nat.eqb k 0 then zero else (if Nat.eqb k 1 then one else undefined)).

Definition fibo_generalized (zero : nat) (one : nat) (rank : nat) :=
  getValue rank (busy nat fibonacci rank (store_fibo zero one)).

Eval compute in fibo_generalized 0 1 5.
