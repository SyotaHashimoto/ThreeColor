
  
From mathcomp Require Import ssreflect ssrbool ssrnat.
 


Variable A X Y Z : Prop.
Hypothesis Ind : (~A -> False) -> A.
  
Lemma syllogism :
 (X -> Y) /\ (Y -> Z) -> (X -> Z). 
Proof.
  move=> [XtoY_is_true YtoZ_is_true X_is_true].
  apply: YtoZ_is_true.
  by exact: XtoY_is_true.
Qed.




