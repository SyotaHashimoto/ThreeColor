From mathcomp
     Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import Classical_Prop.
Require Import PeanoNat Le Lt Plus Mult Even.
Require Import Psatz.
Require Import CoqNat.
Set Implicit Arguments.
Unset Strict Implicit. 
Import Prenex Implicits.

Lemma iff_istrue: forall b:bool, (Bool.Is_true b) <-> b. 
Proof.
  move => b.
  apply conj. move =>H.
  apply Bool.eq_bool_prop_intro.  
  apply conj. by move =>H1. by move =>H1.
  move =>H1. by apply Bool.Is_true_eq_left.      
Qed.

Lemma conv_iff_eql: forall b1 b2: bool, (b1 <-> b2) <-> b1=b2.
Proof.
  move => b1 b2.
  apply conj.
  move => [A B].
  apply Bool.eq_bool_prop_intro.
  apply conj.
  move=>H1. apply iff_istrue. apply iff_istrue in H1. by apply A. 
  move=>H1. apply iff_istrue. apply iff_istrue in H1. by apply B. 
  move=> A. rewrite A. done. 
Qed.

Lemma eql_true: forall b: bool, (b==true) = b. 
Proof.
  by apply eqb_id. 
Qed. 

Lemma eql_false: forall b: bool, (b==false) = ~~b. 
Proof.
    by apply eqbF_neg.
Qed. 

(* double negation elimination *)
Lemma dne_bool: forall b : bool, ~~ ~~ b = b. 
Proof.
    by apply Bool.negb_involutive.
Qed.

Lemma eql_dual_and: forall b1 b2 : bool, ~~ (b1 && b2) = (~~ b1 || ~~ b2).
Proof.
  by apply Bool.negb_andb. 
Qed. 

Lemma eql_dual_or: forall b1 b2 : bool, ~~ (b1 || b2) = (~~ b1 && ~~ b2).
Proof.
  by apply Bool.negb_orb. 
Qed. 
  

Lemma iff_not_eq: forall b1 b2: bool, (~~b1 = b2) <-> (b1 = ~~b2).
Proof.
  move => b1 b2.
  apply conj.
  move => H. rewrite- H. by rewrite dne_bool. 
  move => H. rewrite H. by rewrite dne_bool. 
Qed.

Lemma eql_dual_le: forall m n : nat, ~~ (m <= n) = (n < m). 
Proof.
  move => m n.
  by rewrite ltnNge. 
Qed. 

Lemma eql_dual_lt: forall m n : nat, ~~ (m < n) = (n <= m). 
Proof.
  move => m n. 
  by rewrite eql_dual_le.
Qed.

Lemma eql_dual_eq: forall m n : nat, ~~ (m == n) = (m != n). 
Proof.
  done. 
Qed.

Lemma eql_dual_neq: forall m n : nat, ~~ (m != n) = (m == n). 
Proof.
  move => m n. by apply iff_not_eq. 
Qed.


Lemma eql_comm_plus: forall m n : nat, m+n = n+m.
Proof.
  move=> m n. 
  rewrite ! coqnat_plus. by apply Nat.add_comm. 
Qed.

Lemma eql_assoc_plus: forall m n k : nat, (m+n)+k = m+(n+k).
Proof.
  move=> m n k. 
  rewrite ! coqnat_plus. by apply plus_assoc_reverse.
Qed.


 
 
(* --- 不等式の性質 --- *)
Lemma eql_le_pred_eq_zero: forall n : nat, (n <= n.-1) = (n==0).
Proof.
  move => n. apply conv_iff_eql.
  apply conj. move=> H. 
  rewrite leqNgt in H.
  rewrite (Bool.negb_involutive_reverse (n==0)).
  have A: n != 0 -> n.-1 < n.
  move/eqP. move=>E. apply /coqnat_lt. by apply Nat.lt_pred_l. by apply contra in A.
  move /eqP. move=> H1. rewrite H1. done.
Qed.

Lemma eql_S_lt_lt_P: forall m n : nat, (n.+1 < m) = (n < m.-1).
Proof.
  move => m n. apply conv_iff_eql. by rewrite ltn_predRL.
Qed.

Lemma eql_S_le_lt: forall m n : nat, (m.+1 <= n) = (m < n). 
Proof.
  move=> m n. apply conv_iff_eql. by apply conv_iff_eql.
Qed.

Lemma eql_le_eq_lt: forall m n : nat, (m <= n) = (m == n) || (m < n).
Proof.
    by apply leq_eqVlt.
Qed.

Lemma eql_unit_plus_l: forall n : nat, n + 0 = n. 
Proof.
  move=> n. rewrite coqnat_plus. by rewrite Nat.add_0_r. 
Qed.

Lemma eql_unit_plus_r: forall n : nat, 0 + n = n. 
Proof.
  move=> n. rewrite eql_comm_plus. by apply eql_unit_plus_l. 
Qed.

Lemma eql_mono_plus_lt_plus: forall n m p : nat, (n < m) = ((n + p) < (m + p)). 
Proof.
  move=> n m p. by rewrite ltn_add2r. 
Qed.

Lemma eql_mono_plus_le_plus: forall n m p : nat, (n <= m) = ((n + p) <= (m + p)). 
Proof.
  move=> n m p. by rewrite leq_add2r. 
Qed.

(* zero_lt_add_r *)
Lemma eql_lt_plus_r: forall m n : nat, (0 < n) = (m < n+m). 
Proof.
  move=> m n. apply conv_iff_eql. 
  rewrite- {1} (Nat.add_0_l m).
  rewrite- coqnat_plus.
  by rewrite- eql_mono_plus_lt_plus.
Qed.

(* zero_lt_add_l *)
Lemma eql_lt_plus_l: forall m n : nat, (0 < n) = (m < m+n). 
Proof.
  move=> m n. rewrite eql_comm_plus. by apply eql_lt_plus_r. 
Qed.

Lemma eql_le_plus_r: forall m n : nat, (0 <= n) = (m <= n+m). 
Proof.
  move=> m n. rewrite- {1} (eql_unit_plus_r m). by apply eql_mono_plus_le_plus. 
Qed.

Lemma eql_le_plus_l : forall m n : nat, (0 <= n) = (m <= m+n). 
Proof.
  move=> m n. rewrite eql_comm_plus. by apply eql_le_plus_r.   
Qed.

(* zero_lt_le_add_l *)
Lemma eql_S_le_add_l: forall m n : nat, (0 < n) = (m.+1 <= m+n). 
Proof.
  move=> m n. by apply eql_lt_plus_l. 
Qed.

(* zero_lt_le_add_r *)
Lemma eql_S_le_add_r: forall m n : nat, (0 < n) = (m.+1 <= n+m). 
Proof.
  move=> m n. rewrite (eql_comm_plus n m). by apply eql_S_le_add_l.
Qed.


(* Shifting plus and minus in < and <= *)
Lemma ceql_minus_lt_lt_plus_l: forall p m n: nat, p <= m -> (m-p < n) = (m < p+n).
Proof.
  move=> p m n. by apply ltn_subLR.
Qed.

Lemma ceql_minus_lt_lt_plus_r: forall p m n: nat, p <= m -> (m-p < n) = (m < n+p).
Proof.
  move=> p m n. 
  rewrite (eql_comm_plus n p). by apply ceql_minus_lt_lt_plus_l. 
Qed.

Lemma eql_plus_lt_lt_minus_l: forall p m n: nat, (m+p < n) = (m < n-p).
Proof.
  move=> p m n. rewrite ltn_subRL. by rewrite eql_comm_plus. 
Qed.   

Lemma eql_plus_lt_lt_minus_r: forall p m n: nat, (p+m < n) = (m < n-p).
Proof.
  move=> p m n. 
  rewrite (eql_comm_plus p m). by apply eql_plus_lt_lt_minus_l. 
Qed.

Lemma ceql_plus_le_le_minus_l: forall p m n: nat, p <= n -> (m+p <= n) = (m <= n-p).
Proof.
  move=> p m n A.
  rewrite- (dne_bool (m + p <= n)).
  rewrite- (dne_bool (m <= n-p)).
  rewrite eql_dual_le. rewrite (eql_dual_le m (n - p)).
  by rewrite ceql_minus_lt_lt_plus_r. 
Qed.

Lemma ceql_plus_le_le_minus_r: forall p m n: nat, p <= n -> (p+m <= n) = (m <= n-p).
Proof.
  move=> p m n.
  rewrite (eql_comm_plus p m). by apply ceql_plus_le_le_minus_l.
Qed.

Lemma eql_minus_le_le_plus_l: forall p m n: nat, (m-p <= n) = (m <= n+p).
Proof.
  move=> p m n.
  rewrite- (dne_bool (m - p <= n)).
  rewrite- (dne_bool (m <= n+p)).
  rewrite eql_dual_le. rewrite (eql_dual_le m (n + p)).
  by rewrite eql_plus_lt_lt_minus_l. 
Qed.

Lemma eql_minus_le_le_plus_r: forall p m n: nat, (m-p <= n) = (m <= p+n).
Proof.
  move=> p m n.
  rewrite (eql_comm_plus p n). by apply eql_minus_le_le_plus_l.
Qed.

Lemma ceql_P_lt_lt_S: forall m n: nat, 0 < m -> (m.-1 < n) = (m < n.+1).
Proof.
  move=> m n. rewrite- (addn1 n). rewrite- subn1. apply ceql_minus_lt_lt_plus_r. 
Qed.

Lemma ceql_S_le_le_P: forall m n: nat, 0 < n -> (m.+1 <= n) = (m <= n.-1).
Proof.
  move=> m n. rewrite- subn1. apply ceql_plus_le_le_minus_r.
Qed.


(* transitivity properties of inequalities *)
Lemma trans_lelele: forall p m n : nat, m <= p -> p <= n -> m <= n.
Proof.
    by apply leq_trans.
Qed.   

Lemma trans_ltltlt: forall p m n : nat, m < p -> p < n -> m < n.
Proof.
    by apply ltn_trans.
Qed.   

Lemma trans_leltlt: forall p m n : nat, m <= p -> p < n -> m < n.
Proof.
    by apply leq_ltn_trans.
Qed.

Lemma trans_ltlelt: forall p m n : nat, m < p -> p <= n -> m < n.
Proof.
  move => n m k A B.
  rewrite eql_le_eq_lt in B. move /orP in B.
  move : B. move => [B1|B2]. 
  move /eqP in B1. by rewrite- B1.
  apply (trans_ltltlt A B2).
Qed.

  
  



