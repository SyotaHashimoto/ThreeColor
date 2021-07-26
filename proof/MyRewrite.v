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

Lemma eq_true: forall b: bool, (b==true) = b. 
Proof.
  by apply eqb_id. 
Qed. 

Lemma eq_false: forall b: bool, (b==false) = ~~b. 
Proof.
    by apply eqbF_neg.
Qed. 

Lemma le_bool_true: forall b:bool, b <= true.
Proof.
  move=>b.
  have cond: b || ~~b. apply orbN. move:cond. case/orP =>[tt|ff].
  by rewrite- tt. rewrite- eq_false in ff. move/eqP in ff. by rewrite ff.
Qed. 

Lemma le_bool_false: forall b:bool, false <= b.
Proof.
  move=>b.
  have cond: b || ~~b. apply orbN. move:cond. case/orP =>[tt|ff].
  by rewrite tt. rewrite- eq_false in ff. move/eqP in ff. by rewrite ff.
Qed. 

Lemma conv_bool_eq: forall b1 b2:bool, (b1 = b2) <-> (b1 == b2).
Proof.
  move=> b1 b2. split. move=>H. by rewrite H.
  have cond1: b1 || ~~b1. apply orbN. have cond2: b2 || ~~b2. apply orbN.
  move/orP in cond1. move/orP in cond2. case:cond1 =>[tt1|ff1]. rewrite tt1. 
  case:cond2 =>[tt2|ff2]. by rewrite tt2. rewrite- eq_false in ff2. move/eqP in ff2. by rewrite ff2. 
  rewrite- eq_false in ff1. move/eqP in ff1. rewrite ff1. 
  case:cond2 =>[tt2|ff2]. by rewrite tt2. rewrite- eq_false in ff2. move/eqP in ff2. by rewrite ff2.   
Qed.

Lemma eq_contrapos: forall b1 b2:bool, (b1 == b2) = (~~b1 == ~~b2). 
Proof.
  move=> b1 b2.
  have cond1: b1 || ~~b1. apply orbN. have cond2: b2 || ~~b2. apply orbN.
  move/orP in cond1. move/orP in cond2. case:cond1 =>[tt1|ff1]. rewrite tt1. 
  case:cond2 =>[tt2|ff2]. by rewrite tt2. rewrite- eq_false in ff2. move/eqP in ff2. by rewrite ff2. 
  rewrite- eq_false in ff1. move/eqP in ff1. rewrite ff1. 
  case:cond2 =>[tt2|ff2]. by rewrite tt2. rewrite- eq_false in ff2. move/eqP in ff2. by rewrite ff2.   
Qed.
  
(* double negation elimination *)
Lemma dne_bool: forall b : bool, ~~ ~~ b = b. 
Proof.
    by apply Bool.negb_involutive.
Qed.

Lemma eq_dual_and: forall b1 b2 : bool, ~~ (b1 && b2) = (~~ b1 || ~~ b2).
Proof.
  by apply Bool.negb_andb. 
Qed. 

Lemma eq_dual_or: forall b1 b2 : bool, ~~ (b1 || b2) = (~~ b1 && ~~ b2).
Proof.
  by apply Bool.negb_orb. 
Qed. 
  

Lemma iff_not_eq: forall b1 b2: bool, (~~b1 == b2) <-> (b1 == ~~b2).
Proof.
  move => b1 b2.
  apply conj.
  move => H. move/eqP in H. rewrite- H. by rewrite dne_bool. 
  move => H. move/eqP in H. rewrite H. by rewrite dne_bool. 
Qed.

Lemma eq_not_eq: forall b1 b2: bool, (~~b1 == b2) = (b1 == ~~b2).
Proof.
  move=> b1 b2. apply/conv_iff_eql. apply iff_not_eq. 
Qed.


Lemma eq_dual_le: forall m n : nat, ~~ (m <= n) = (n < m). 
Proof.
  move => m n.
  by rewrite ltnNge. 
Qed. 

Lemma eq_dual_lt: forall m n : nat, ~~ (m < n) = (n <= m). 
Proof.
  move => m n. 
  by rewrite eq_dual_le.
Qed.

Lemma eq_dual_eq: forall m n : nat, ~~ (m == n) = (m != n). 
Proof.
  done. 
Qed.

Lemma eq_dual_neq: forall m n : nat, ~~ (m != n) = (m == n). 
Proof.
  move => m n. apply/eqP. by rewrite eq_not_eq. 
Qed.

Lemma eq_comm_plus: forall m n : nat, m+n = n+m.
Proof.
  move=> m n. 
  rewrite ! coqnat_plus. by apply Nat.add_comm. 
Qed.

Lemma eq_assoc_plus: forall m n k : nat, (m+n)+k = m+(n+k).
Proof.
  move=> m n k. 
  rewrite ! coqnat_plus. by apply plus_assoc_reverse.
Qed.

(* --- Properties about equality --- *)
Lemma eq_mono_plus_eq_r: forall p m n : nat, (m == n) = ((m+p) == (n+p)). 
Proof.
  move=> p m n. symmetry. apply eqn_add2r. 
Qed. 

Lemma eq_mono_plus_eq_plus_l: forall p m n : nat, (m == n) = ((p+m) == (p+n)). 
Proof.
  move=> p m n. symmetry. apply eqn_add2l. 
Qed. 

Lemma eq_zero_plus_r: forall m n : nat, (m == 0) = (m+n == n). 
Proof.
  move=> m n. rewrite- {2} (add0n n). apply (eq_mono_plus_eq_r n m 0). 
Qed. 

Lemma eq_zero_plus_l: forall m n : nat, (m == 0) = (n+m == n). 
Proof.
  move=> m n. rewrite- {2} (addn0 n). apply (eq_mono_plus_eq_plus_l n m 0). 
Qed. 

Lemma eq_lele_eq: forall m n : nat, (m <= n <= m) = (m == n).
Proof.
  move=> m n. symmetry. apply eqn_leq.
Qed.

Lemma eq_mono_succ_eq: forall m n : nat, (m == n) = (m.+1 == n.+1). 
Proof.
  move=> m n. rewrite- (addn1 m). rewrite- (addn1 n). apply eq_mono_plus_eq_r.
Qed. 


(* --- Properties about inequalities --- *)
Lemma eq_le_pred_eq_zero: forall n : nat, (n <= n.-1) = (n==0).
Proof.
  move => n. apply conv_iff_eql.
  apply conj. move=> H. 
  rewrite leqNgt in H.
  rewrite (Bool.negb_involutive_reverse (n==0)).
  have A: n != 0 -> n.-1 < n.
  move/eqP. move=>E. apply /coqnat_lt. by apply Nat.lt_pred_l. by apply contra in A.
  move /eqP. move=> H1. rewrite H1. done.
Qed.

Lemma eq_S_lt_P: forall m n : nat, (n.+1 < m) = (n < m.-1).
Proof.
  move => m n. apply conv_iff_eql. by rewrite ltn_predRL.
Qed.

Lemma eq_S_le_lt: forall m n : nat, (m.+1 <= n) = (m < n). 
Proof.
  move=> m n. apply conv_iff_eql. by apply conv_iff_eql.
Qed.

Lemma eq_le_eq_lt: forall m n : nat, (m <= n) = (m == n) || (m < n).
Proof.
    by apply leq_eqVlt.
Qed.

Lemma eq_unit_plus_l: forall n : nat, n + 0 = n. 
Proof.
  move=> n. rewrite coqnat_plus. by rewrite Nat.add_0_r. 
Qed.

Lemma eq_unit_plus_r: forall n : nat, 0 + n = n. 
Proof.
  move=> n. rewrite eq_comm_plus. by apply eq_unit_plus_l. 
Qed.

Lemma eq_mono_plus_lt_plus: forall n m p : nat, (n < m) = ((n + p) < (m + p)). 
Proof.
  move=> n m p. by rewrite ltn_add2r. 
Qed.

Lemma eq_mono_plus_le_plus: forall n m p : nat, (n <= m) = ((n + p) <= (m + p)). 
Proof.
  move=> n m p. by rewrite leq_add2r. 
Qed.

Lemma eq_mono_succ_le: forall m n : nat, (m <= n) = (m.+1 <= n.+1). 
Proof.
  move=> m n. rewrite- (addn1 m). rewrite- (addn1 n). apply eq_mono_plus_le_plus.
Qed. 

Lemma eq_mono_succ_lt: forall m n : nat, (m < n) = (m.+1 < n.+1). 
Proof.
  move=> m n. rewrite- {2} (addn1 m). rewrite- (addn1 n). apply eq_mono_plus_lt_plus. 
Qed. 


Lemma eq_lt_plus_r: forall m n : nat, (0 < n) = (m < n+m). 
Proof.
  move=> m n. apply conv_iff_eql. 
  rewrite- {1} (Nat.add_0_l m).
  rewrite- coqnat_plus.
  by rewrite- eq_mono_plus_lt_plus.
Qed.

Lemma eq_lt_plus_l: forall m n : nat, (0 < n) = (m < m+n). 
Proof.
  move=> m n. rewrite eq_comm_plus. by apply eq_lt_plus_r. 
Qed.

Lemma eq_le_plus_r: forall m n : nat, (0 <= n) = (m <= n+m). 
Proof.
  move=> m n. rewrite- {1} (eq_unit_plus_r m). by apply eq_mono_plus_le_plus. 
Qed.

Lemma eq_le_plus_l : forall m n : nat, (0 <= n) = (m <= m+n). 
Proof.
  move=> m n. rewrite eq_comm_plus. by apply eq_le_plus_r.   
Qed.

Lemma eq_S_le_add_l: forall m n : nat, (0 < n) = (m.+1 <= m+n). 
Proof.
  move=> m n. by apply eq_lt_plus_l. 
Qed.

Lemma eq_S_le_add_r: forall m n : nat, (0 < n) = (m.+1 <= n+m). 
Proof.
  move=> m n. rewrite (eq_comm_plus n m). by apply eq_S_le_add_l.
Qed.

(* transitivity *)
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
  rewrite eq_le_eq_lt in B. move /orP in B.
  move : B. move => [B1|B2]. 
  move /eqP in B1. by rewrite- B1.
  apply (trans_ltltlt A B2).
Qed.

(* Adjointnesses of plus and minus *)
(* eq_minus_lt_plus_l *)
Lemma eq_adjoint_minus_plus_lt': forall p m n: nat, p <= m -> (m-p < n) = (m < p+n).
Proof.
  move=> p m n. by apply ltn_subLR.
Qed.

(* eq_minus_lt_plus_r *)
Lemma eq_adjoint_minus_plus_lt: forall p m n: nat, p <= m -> (m-p < n) = (m < n+p).
Proof.
  move=> p m n. 
  rewrite (eq_comm_plus n p). by apply eq_adjoint_minus_plus_lt'. 
Qed.

(* eq_plus_lt_minus_l *)
Lemma eq_adjoint_plus_minus_lt: forall p m n: nat, (m+p < n) = (m < n-p).
Proof.
  move=> p m n. rewrite ltn_subRL. by rewrite eq_comm_plus. 
Qed.   

(* eq_plus_lt_minus_r *)
Lemma eq_adjoint_plus_minus_lt': forall p m n: nat, (p+m < n) = (m < n-p).
Proof.
  move=> p m n. rewrite (eq_comm_plus p m). by apply eq_adjoint_plus_minus_lt. 
Qed.

(* eq_plus_le_le_minus_l *)
Lemma eq_adjoint_plus_minus_le: forall p m n: nat, p <= n -> (m+p <= n) = (m <= n-p).
Proof.
  move=> p m n A.
  rewrite- (dne_bool (m + p <= n)).
  rewrite- (dne_bool (m <= n-p)).
  rewrite eq_dual_le. rewrite (eq_dual_le m (n - p)). by rewrite eq_adjoint_minus_plus_lt.
Qed.

(* eq_plus_le_minus_r *)
Lemma eq_adjoint_plus_minus_le': forall p m n: nat, p <= n -> (p+m <= n) = (m <= n-p).
Proof.
  move=> p m n.
  rewrite (eq_comm_plus p m). by apply eq_adjoint_plus_minus_le.
Qed.

(* eq_minus_le_plus_l *)
Lemma eq_adjoint_minus_plus_le: forall p m n: nat, (m-p <= n) = (m <= n+p).
Proof.
  move=> p m n.
  rewrite- (dne_bool (m - p <= n)).
  rewrite- (dne_bool (m <= n+p)).
  rewrite eq_dual_le. rewrite (eq_dual_le m (n + p)).
  by rewrite eq_adjoint_plus_minus_lt. 
Qed.

(* eq_minus_le_plus_r *)
Lemma eq_adjoint_minus_plus_le': forall p m n: nat, (m-p <= n) = (m <= p+n).
Proof.
  move=> p m n.
  rewrite (eq_comm_plus p n). by apply eq_adjoint_minus_plus_le.
Qed.

(* eq_P_lt_S *)
Lemma eq_adjoint_P_S_lt: forall m n: nat, 0 < m -> (m.-1 < n) = (m < n.+1).
Proof.
  move=> m n. rewrite- (addn1 n). rewrite- subn1. apply eq_adjoint_minus_plus_lt. 
Qed.

Lemma eq_adjoint_P_S_le: forall m n: nat, (m.-1 <= n) = (m <= n.+1).
Proof.
  move=> m n. rewrite- (addn1 n). rewrite- subn1. apply eq_adjoint_minus_plus_le. 
Qed.

(* eq_S_le_P *)
Lemma eq_adjoint_S_P_le: forall m n: nat, 0 < n -> (m.+1 <= n) = (m <= n.-1).
Proof.
  move=> m n. rewrite- subn1. apply eq_adjoint_plus_minus_le'.
Qed.

Lemma eq_adjoint_S_P_lt: forall m n: nat, (m.+1 < n) = (m < n.-1).
Proof.
  move=> m n. rewrite- subn1. rewrite- {1} (addn1 m). apply eq_adjoint_plus_minus_lt.
Qed.

Lemma eq_adjoint_plus_minus_eq: forall p m n: nat, p <= n -> (m+p == n) = (m == n-p).
Proof.
  move=> p m n H. 
  have A: (m + p <= n) = (m <= n - p). by rewrite eq_adjoint_plus_minus_le. 
  have B: (n <= m + p) = (n - p <= m). by rewrite eq_adjoint_minus_plus_le.
  rewrite- !eq_lele_eq. rewrite A. rewrite B. done. 
Qed.

Lemma eq_adjoint_minus_plus_eq: forall p m n: nat, p <= m -> (m-p == n) = (m == n+p).
Proof.
  move=> p m n H. symmetry. rewrite eq_sym. rewrite (eq_sym (m-p) n). by apply eq_adjoint_plus_minus_eq. 
Qed.  

Lemma eq_adjoint_S_P_eq: forall m n: nat, 0 < n -> (m.+1 == n) = (m == n.-1).
Proof.
  move=> m n H. 
  have A: (m.+1 <= n) = (m <= n.-1). by rewrite eq_adjoint_S_P_le. 
  have B: (n <= m.+1) = (n.-1 <= m). by rewrite eq_adjoint_P_S_le.
  rewrite- !eq_lele_eq. rewrite A. rewrite B. done. 
Qed.

Lemma eq_adjoint_P_S_eq: forall m n: nat, 0 < m -> (m.-1 == n) = (m == n.+1).
Proof.
  move=> m n H. symmetry. rewrite eq_sym. rewrite (eq_sym (m.-1) n). by apply eq_adjoint_S_P_eq. 
Qed.  

(* odd and even *)
Lemma conv_Odd_Nat_odd: forall m: nat, Nat.Odd m <->  Nat.odd m. 
Proof.
  move=> m. symmetry. apply Nat.odd_spec.
Qed.

Lemma conv_Even_Nat_even: forall m: nat, Nat.Even m <->  Nat.even m. 
Proof.
  move=> m. symmetry. apply Nat.even_spec.
Qed.

Lemma conv_OddEven_oddeven: forall m: nat, (Nat.Odd m <-> ssrnat.odd m) /\ (Nat.Even m <-> ~~ssrnat.odd m). 
Proof.
  move=> m. elim m. split.  apply/conv_Odd_Nat_odd. apply/conv_Even_Nat_even.
  move=> n [ind1 ind2].
  split.  
  have A: Nat.Odd n.+1 <-> Nat.Even n. by apply Nat.Odd_succ. apply (iff_trans A). apply (iff_trans ind2). done. 
  have B: Nat.Even n.+1 <-> Nat.Odd n. by apply Nat.Even_succ. apply (iff_trans B). apply (iff_trans ind1).
  simpl. by rewrite dne_bool.
Qed.

Lemma conv_Odd_odd: forall m: nat, Nat.Odd m <-> ssrnat.odd m. 
Proof.
  move=>m.
  have A: (Nat.Odd m <-> ssrnat.odd m) /\ (Nat.Even m <-> ~~ssrnat.odd m). apply conv_OddEven_oddeven. 
  by apply proj1 in A. 
Qed.

Lemma conv_Even_even: forall m: nat, Nat.Even m <-> ~~ssrnat.odd m. 
Proof.
  move=>m.
  have A: (Nat.Odd m <-> ssrnat.odd m) /\ (Nat.Even m <-> ~~ssrnat.odd m). apply conv_OddEven_oddeven. 
  by apply proj2 in A. 
Qed.

Lemma eq_odd: forall m: nat, Nat.odd m = ssrnat.odd m.
Proof.
  move=>m. have H: Nat.odd m <-> ssrnat.odd m.
  apply (iff_trans (iff_sym (conv_Odd_Nat_odd m))). apply conv_Odd_odd. by apply conv_iff_eql. 
Qed.
  
Lemma eq_even: forall m: nat, Nat.even m = ~~ssrnat.odd m.
Proof.
  move=>m. have H: Nat.even m <-> ~~ssrnat.odd m.
  apply (iff_trans (iff_sym (conv_Even_Nat_even m))). apply conv_Even_even. by apply conv_iff_eql. 
Qed.

Lemma eq_even_plus: forall m n: nat, ~~ssrnat.odd m -> ssrnat.odd (m+n) = ssrnat.odd n.
Proof.
  move=> m n H. move/conv_Even_even in H. 
  rewrite- !eq_odd. rewrite eq_comm_plus. by rewrite Nat.odd_add_even.
Qed.
  
Lemma eq_odd_plus: forall m n: nat, ssrnat.odd m -> ssrnat.odd (m+n) = ~~ssrnat.odd n.
Proof.
  move=> m n H. have A: m>0. by apply odd_gt0.
  have B: m = (m.-1).+1. apply S_pred_pos. by apply/ltP.
  rewrite B in H. simpl in H. rewrite B.
  have C: ssrnat.odd (m.-1+n) = ssrnat.odd n. by apply eq_even_plus.
  rewrite- C. done.
Qed.

(* Properties about double and half *)
Lemma eq_half_double_even: forall m: nat, ~~ssrnat.odd m -> ((m./2).*2 = m). 
Proof.
  move=> m even. rewrite- {2} (odd_double_half m).
  have A: ssrnat.odd m = false. by apply negbTE. rewrite A. simpl. by rewrite add0n.
Qed.

Lemma eq_half_double_odd: forall m: nat, ssrnat.odd m -> (((m./2).*2).+1 = m). 
Proof.
  move=> m odd.
  have A: (((m./2).*2)+(ssrnat.odd m) = m). rewrite eq_comm_plus. apply odd_double_half.
  rewrite- {2} A. rewrite- addn1. apply/eqP. rewrite- eq_mono_plus_eq_plus_l. rewrite odd. done.
Qed.

Lemma eq_double_half: forall m: nat, (m.*2)./2 = m. 
Proof.
  move=>m. have H: (m.*2)./2 = 0+m. apply (half_bit_double m false). rewrite add0n in H. done. 
Qed.

Lemma eq_mono_double_le: forall m n: nat, (m <= n) = (m.*2 <= n.*2).
Proof.
  move=> m n. symmetry. apply leq_double. 
Qed.

Lemma eq_mono_double_eq: forall m n: nat, (m == n) = (m.*2 == n.*2).
Proof.
  move=> m n.
  have A: (m<=n) = (m.*2 <= n.*2). by apply eq_mono_double_le. 
  have B: (n<=m) = (n.*2 <= m.*2). by apply eq_mono_double_le. 
  have AB: (m<=n<=m) = (m.*2 <= n.*2 <= m.*2).
  rewrite A. rewrite B. done. by rewrite- !eq_lele_eq. 
Qed.

Lemma eq_mono_double_lt: forall m n: nat, (m < n) = (m.*2 < n.*2).
Proof.
  move=> m n. rewrite- !eq_dual_le. rewrite eq_mono_double_le. done. 
Qed.

Lemma imp_mono_half_le: forall m n: nat, (m <= n) -> (m./2 <= n./2).
Proof.
  move=> m n H. by apply half_leq. 
Qed.

Lemma rev_mono_half_le: forall m n: nat, (ssrnat.odd m <= ssrnat.odd n) -> (m./2 <= n./2) -> (m <= n).
Proof.
  move=> m n H A.
  have condN: ssrnat.odd n || ~~ssrnat.odd n. apply orbN. move:condN. case/orP =>[oddN|evenN].
  have condM: ssrnat.odd m || ~~ssrnat.odd m. apply orbN. move:condM. case/orP =>[oddM|evenM].
  - rewrite- (eq_half_double_odd oddN). rewrite- (eq_half_double_odd oddM). 
    rewrite- eq_mono_succ_le. by rewrite- eq_mono_double_le.
  - rewrite- (eq_half_double_odd oddN). rewrite- (eq_half_double_even evenM).
    have B: (m./2).*2 <= (n./2).*2. by rewrite- eq_mono_double_le.
    apply (trans_lelele B). apply leqnSn.
  - have evenM: ~~ssrnat.odd m. rewrite- eq_false in evenN. move/eqP in evenN. rewrite evenN in H.
    apply/negP. move=>C. rewrite C in H. done. 
    rewrite- (eq_half_double_even evenN). rewrite- (eq_half_double_even evenM). by rewrite- eq_mono_double_le.
Qed.

Lemma eq_mono_half_le: forall m n: nat, (ssrnat.odd m <= ssrnat.odd n) -> (m <= n) = (m./2 <= n./2).
Proof.
  move=> m n H. symmetry. have A: (m./2 <= n./2) <-> (m <= n). split. by apply rev_mono_half_le.
  apply imp_mono_half_le. by apply conv_iff_eql.
Qed.
  
Lemma eq_mono_half_eq: forall m n: nat, (ssrnat.odd m == ssrnat.odd n) -> (m == n) = (m./2 == n./2).
Proof.
  move=> m n H. move/eqP in H.
  have A: (m <= n) = (m./2 <= n./2). apply eq_mono_half_le. by rewrite H.
  have B: (n <= m) = (n./2 <= m./2). apply eq_mono_half_le. by rewrite H.
  rewrite- eq_lele_eq. rewrite A. rewrite B. by rewrite eq_lele_eq.
Qed.

Lemma imp_mono_half_lt: forall m n: nat, (ssrnat.odd n <= ssrnat.odd m) -> (m < n) = (m./2 < n./2).
Proof.
  move=> m n H.
  rewrite- !eq_dual_le. rewrite eq_mono_half_le. done. done. 
Qed.


(* Adjointnesses of double and half *)
Lemma eq_adjoint_double_half_le: forall m n: nat, (m.*2 <= n) = (m <= n./2).
Proof.
  move=> m n.
  have condN: ssrnat.odd n || ~~ssrnat.odd n. apply orbN. move:condN. case/orP =>[oddN|evenN].
  rewrite eq_mono_half_le. by rewrite eq_double_half. rewrite oddN. apply le_bool_true. 
  rewrite eq_mono_half_le. by rewrite eq_double_half. rewrite- eq_false in evenN.
  move/eqP in evenN. rewrite evenN. by rewrite odd_double.
Qed. 

Lemma eq_adjoint_half_double_le: forall m n: nat, ~~(ssrnat.odd m) -> (m./2 <= n) = (m <= n.*2).
Proof.
  move=> m n evenM.
  have evenN2: ~~ssrnat.odd (n.*2). by rewrite odd_double.
  have cond: ssrnat.odd m <= ssrnat.odd (n.*2).
  rewrite- eq_false in evenM. move/eqP in evenM. rewrite evenM.
  rewrite- eq_false in evenN2. move/eqP in evenN2. rewrite evenN2. done. 
  rewrite (eq_mono_half_le cond). by rewrite eq_double_half. 
Qed.  
  
Lemma eq_adjoint_double_half_lt: forall m n: nat, ~~(ssrnat.odd n) -> (m.*2 < n) = (m < n./2).
  move=> m n evenN. have A: ~~(m < n./2) = ~~(m.*2 < n).
  rewrite !eq_dual_lt. by rewrite eq_adjoint_half_double_le. 
  rewrite- (dne_bool (m.*2 < n)). rewrite- (dne_bool (m < n./2)).
  by rewrite A. 
Qed.

Lemma eq_adjoint_half_double_lt: forall m n: nat, (m./2 < n) = (m < n.*2).
Proof.
  move=> m n. have A: ~~(m < n.*2) = ~~(m./2 < n).
  rewrite !eq_dual_lt. by rewrite eq_adjoint_double_half_le. 
  rewrite- (dne_bool (m./2 < n)). rewrite- (dne_bool (m < n.*2)).
  by rewrite A. 
Qed.

Lemma eq_adjoint_double_half_eq: forall m n: nat, ~~(ssrnat.odd n) -> (m.*2 == n) = (m == n./2).
  move=> m n H. 
  have A: (m.*2 <= n) = (m <= n./2). by rewrite eq_adjoint_double_half_le. 
  have B: (n <= m.*2) = (n./2 <= m). by rewrite eq_adjoint_half_double_le.
  rewrite- !eq_lele_eq. rewrite A. rewrite B. done. 
Qed.

Lemma eq_adjoint_half_double_eq: forall m n: nat, ~~(ssrnat.odd m) -> (m./2 == n) = (m == n.*2).
Proof.
  move=> m n H. 
  have A: (m./2 <= n) = (m <= n.*2). by rewrite eq_adjoint_half_double_le. 
  have B: (n <= m./2) = (n.*2 <= m). by rewrite eq_adjoint_double_half_le.
  rewrite- !eq_lele_eq. rewrite A. rewrite B. done. 
Qed.
