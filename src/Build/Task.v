Require Import Coq.Vectors.Fin.
Require Import Data.Maybe.
Require Import Data.Functor.
Require Import Control.Monad.
Require Import Control.Monad.State.
Require Import Build.Store.

(* (* The Task abstraction *) *)
(* Record Task (C : (Type -> Type) -> Type) (K V : Type) := *)
(*   mkTask {key : K; run : forall F `{C F}, ((K -> F V) -> F V)}. *)

(* Record Task1 (V : Type) := *)
(*   mkTask1 { key1 : nat *)
(*           ; run1 : forall F `{Monad F}, (nat -> F V) -> nat -> Maybe (F V)}. *)

(* Record Task := *)
(*   mkTask { key : nat *)
(*          ; run : forall F `{Monad F}, (forall k : nat, k < key -> F unit) -> *)
(*                                        nat -> *)
(*                                        Maybe (F unit)}. *)

Definition ST := State (Store unit nat unit).

(* Record Task := *)
(*   mkTask { key : nat *)
(*            ; run (k : nat) : ((k, (k < key)) ->  unit) -> *)
(*                              Maybe (ST unit)}. *)

Record Task :=
  mkTask { key : nat
         ; run  : ({k | k < key} -> ST unit) -> Maybe (ST unit)}.
