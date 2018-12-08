Require Import Control.Monad.
Require Import Data.Functor.Identity.
Require Import Build.Store.
Require Import Build.AcyclicTask.

(* -- | Run a task in a given store. *)
Definition compute (I K V : Type) (task : Task Monad K V) (store : Store I K V) : V :=
  runIdentity ((run task) (fun k => mkIdentity (getValue k store))).