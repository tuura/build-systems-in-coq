Require Coq.Program.Tactics.
Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Monad.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************
 * The State Monad
 *)

Inductive State (s a : Type) :=
  state : (s -> (a * s)) -> State s a.

Definition runState {s a : Type}
  (computation : State s a) (initial : s) : (a * s) :=
  match computation with
  | state f => f initial
  end.

Definition get  {s : Type}     : State s s := state (fun i => (i, i)).
Definition gets {s a : Type} f : State s a := state (fun s => (f s, s)).
Definition put  {s : Type} x   : State s unit := state (fun _ => (tt, x)).

Definition modify {s : Type} (f : s -> s) : State s unit := state (fun i => (tt, f i)).

Instance State_Functor {s : Type} : Functor (State s) := {
  fmap := fun A B f (x : State s A) =>
    state (fun st => match runState x st with
                     | (a,st') => (f a, st')
                     end)
}.

Instance State_Applicative {s : Type} : Applicative (State s) := {
  pure := fun _ x => state (fun st => (x, st));

  ap := fun _ _ f x => state (fun st => match runState f st with
    | (f', st') =>
        match runState x st' with
        | (x', st'') => (f' x', st'')
        end
    end)
}.

Instance State_Monad {s : Type} : Monad (State s) := {
  join := fun _ x => state (fun st => match runState x st with
    | (y, st') => match runState y st' with
      | (a, st'') => (a, st'')
      end
    end)
}.
