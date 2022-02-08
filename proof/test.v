Require Import PeanoNat Le Lt Plus Mult Even.
From mathcomp
     Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import Classical_Prop.
Require Import Psatz.
Require Import CoqNat MyRewrite.
Inductive Color : Set :=
| red
| yel
| blu.
Variable Cpos :  nat -> nat -> Color -> Prop.
Hypothesis C_uniq :
   forall x y : nat, forall c0 c1 : Color, (Cpos x y c0 /\ Cpos x y c1) -> c0 = c1.
Axiom C_paint : forall x i : nat, forall f:nat -> Color, Cpos (x+i) 0 (f (x+i)).
Lemma Contra: False.
Proof.
  have R: Cpos 0 0 red.
  apply (C_paint 0 0 (fun x:nat=>red)).
  have B: Cpos 0 0 blu.
  apply (C_paint 0 0 (fun x:nat=>blu)).
  have RB: red=blu.
  apply (C_uniq 0 0). done.
  move:RB. done.
Qed.
