Require Import Data.Functor.
Require Import Control.Applicative.
Require Import Data.Monoid.

(* The Conts datatype *)
Inductive Const (A B: Type) :=
  mkConst {getConst : A}.

Arguments mkConst {_} {_} _.
Arguments getConst {_} {_} _.

Instance Const_Functor {C : Type} : Functor (Const C) :=
  {
    fmap {A} {B} f c := match c with
                        | mkConst x => mkConst x
                        end
  }.

(* instance Monoid m => Applicative (Const m) where *)
(*     pure _ = Const mempty *)
(*     liftA2 _ (Const x) (Const y) = Const (x `mappend` y) *)
(*     (<*>) = coerce (mappend :: m -> m -> m) *)

Check pure.

Instance Const_Applicative {C : Type} `{Monoid C}: Applicative (Const C) :=
  {
    pure _ := fun _ => mkConst mempty;
    ap _ _ a b := match a, b with
                  | mkConst x, mkConst y => mkConst (mappend x y)
                  end
  }.