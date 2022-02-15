


Require Import ssreflect.
 
Variable X Y : Prop.
Hypothesis X_is_true : X.
Hypothesis XtoY_is_true : X -> Y.

Lemma lemma_name : Y.
Proof.
  move: X_is_true.
  by apply: XtoY_is_true.
Qed.




