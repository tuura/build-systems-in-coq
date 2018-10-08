Require Import Eq.
Require Import Data.Maybe.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Monad.
Require Import Control.Monad.State.
Require Import Build.
Require Import Build.Task.
Require Import Build.Store.

Require Import Omega.
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


(* Definition busy (V : Type) (tasks : Tasks Monad nat V) (key : nat) *)
(*            (store : Store unit nat V) : Store unit nat V := *)
(*   let fix fetch (k : nat) : State (Store unit nat V) V := *)
(*       match tasks k with *)
(*       | Nothing => gets (getValue k) *)
(*       | Just task => *)
(*             let t := run Monad nat V task (State (Store unit nat V)) in *)
(*             let f := fetch in *)
(*             (run Monad nat V task (State (Store unit nat V))) (fetch) >>= *)
(*             fun (v : V) => undefined *)
(*       end *)
(*   in snd ((fetch key) store). *)

(* Definition runM {V : Type} (task : Task Monad nat V) : *)
(*   (nat -> State (Store unit nat V) V) -> State (Store unit nat V) V := *)
(*   run Monad nat V task (State (Store unit nat V)). *)

Fixpoint eq_nat_impl n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat_impl n1 m1
  end.

Instance eq_nat : Eq nat := { eqb := eq_nat_impl}.

(* Program Fixpoint busyFetch1 {V : Type} (task : Task1 V) (k : nat) *)
(*   {measure k}: *)
(*   State (Store unit nat V) V := *)
(*   let t := ((runM1 task) (busyFetch1 task)) k in *)
(*   match t with *)
(*   | Nothing  => gets (getValue k) *)
(*   | Just act => *)
(*       act >>= *)
(*       fun (v : V) => modify (putValue k v) >> pure v *)
(*   end. *)
(* Next Obligation. *)
(* Proof. *)

Lemma zgtz : 0 > 0 -> False.
Proof.
  omega.
Qed.

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
    | exist _ O pf => match zgtz pf with end
    | exist _ (S n') _ => n'
  end.

Program Fixpoint busyFetch (task : Task) (s : {k : nat | k < key task})
  {measure (key task)}:
  ST unit :=
  match s with
  | O      => undefined
  | (S k') =>
    let t := ((run task) (busyFetch task (proj2_sig k'))) s in
    match t with
    | Nothing  => gets (getValue (S k'))
    | Just act =>
      act >>=
          fun v => modify (putValue (S k') v) >> pure v
    end
  end.
