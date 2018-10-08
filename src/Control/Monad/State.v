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

Definition State (s a : Type) := s -> (a * s).

Definition get  {s : Type}     : State s s := fun i => (i, i).
Definition gets {s a : Type} f : State s a := fun s => (f s, s).
Definition put  {s : Type} x   : State s unit := fun _ => (tt, x).

Definition modify {s : Type} (f : s -> s) : State s unit := fun i => (tt, f i).

Instance State_Functor {s : Type} : Functor (State s) := {
  fmap := fun A B f (x : State s A) => fun st => match x st with
    | (a,st') => (f a, st')
    end
}.

Instance State_Applicative {s : Type} : Applicative (State s) := {
  pure := fun _ x => fun st => (x, st);

  ap := fun _ _ f x => fun st => match f st with
    | (f', st') =>
        match x st' with
        | (x', st'') => (f' x', st'')
        end
    end
}.

Instance State_Monad {s : Type} : Monad (State s) := {
  join := fun _ x => fun st => match x st with
    | (y, st') => match y st' with
      | (a, st'') => (a, st'')
      end
    end
}.
