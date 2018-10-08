Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Control.Monad.

Inductive Proxy (A : Type): Type :=
  | proxy : Proxy A.

Arguments proxy {A}.

Instance Proxy_Functor : Functor Proxy := {
  fmap := fun A B _ _ => proxy
}.

Instance Proxy_Applicative : Applicative Proxy := {
  pure := fun A _ => proxy;
  ap := fun _ B f x => proxy;
}.

Instance Proxy_Monad : Monad Proxy := {
  join := fun A x => proxy
}.
