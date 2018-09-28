Require Import Data.Functor.

(* The Conts datatype *)
Record Const (A B: Type) :=
  mkConst {getConst : A}.

Instance Const_Functor {C : Type} : Functor (Const C) :=
  {
    fmap {A} {B} f c := match c with
                        | mkConst _ _ x => mkConst C B x
                        end
  }.