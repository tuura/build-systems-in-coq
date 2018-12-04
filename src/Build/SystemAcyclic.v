Require Import Data.Maybe.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Monad.
Require Import Control.Monad.State.
Require Import Build.AcyclicTask.
Require Import Build.Store.

Require Import Omega.
Require Import Coq.Program.Wf.
Require Import Coq.Vectors.Fin.

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

(* Program Fixpoint test (k : nat) (todo : t k) {measure k} :=
  let k' := (proj1_sig (to_nat todo)) in test k' (from_nat k'). *)
Program Fixpoint busyFetch (V : Type) (tasks : AcyclicTasks Applicative V) (k:nat) 
  {measure k}
  : State (Store unit nat V) V :=
  match tasks k with
  | Nothing   => gets (getValue k)
  | Just task => 
    (run task) (fun n => busyFetch V tasks (proj1_sig n))
  end.

(* >>=
    (fun v => modify (putValue k v) >>= (fun _ => pure v)) *)
Definition busy (V : Type) (tasks : AcyclicTasks Applicative V) (key : nat)
           (store : Store unit nat V) : Store unit nat V :=
  snd ((busyFetch V tasks key) store).

Eval compute in deps_fib (S (S 1)).

(* Definition runM {V : Type} (task : Task Monad nat V) : *)
(*   (nat -> State (Store unit nat V) V) -> State (Store unit nat V) V := *)
(*   run Monad nat V task (State (Store unit nat V)). *)
