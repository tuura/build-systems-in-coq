Require Import Data.Functor.
Require Import Data.Functor.Const.
Require Import Build.Task.

(* -- | Find the dependency of a functorial task. *)
(* dependency :: Task Functor k v -> k *)
(* dependency task = getConst $ run task Const *)
Definition dependency {K V: Type} (task : Task Functor K V) : K :=
  getConst K V ((run Functor K V task (Const K)) (mkConst K V)).