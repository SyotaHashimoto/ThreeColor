From mathcomp
     Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
(*
Require Import PeanoNat Le Lt Plus Mult Even.
Require Import Classical_Prop.
Require Import Psatz.
*)
Set Implicit Arguments.
Unset Strict Implicit. 
Import Prenex Implicits.

Lemma conv_iff_eql: forall b1 b2: bool, (b1 <-> b2) <-> b1=b2.
Proof.
  move => b1 b2. split. move => [A B]. 
  apply Bool.eq_bool_prop_intro. split. 
  move=>H1. apply Bool.Is_true_eq_left. apply Bool.Is_true_eq_true in H1. by apply A. 
  move=>H1. apply Bool.Is_true_eq_left. apply Bool.Is_true_eq_true in H1. by apply B. 
  move=>H. rewrite H. done. 
Qed.

Lemma le_bool_true: forall b:bool, b <= true.
Proof.
  move=>b.
  have cond: b || ~~b. apply orbN. move:cond. case/orP =>[tt|ff].
  by rewrite- tt. rewrite- eqbF_neg in ff. move/eqP in ff. by rewrite ff.
Qed. 

Lemma le_bool_false: forall b:bool, false <= b.
Proof.
  move=>b.
  have cond: b || ~~b. apply orbN. move:cond. case/orP =>[tt|ff].
  by rewrite tt. rewrite- eqbF_neg in ff. move/eqP in ff. by rewrite ff.
Qed. 

Lemma conv_bool_eq: forall b1 b2:bool, (b1 = b2) <-> (b1 == b2).
Proof.
  move=> b1 b2. split. move=>H. by rewrite H.
  have cond1: b1 || ~~b1. apply orbN. have cond2: b2 || ~~b2. apply orbN.
  move/orP in cond1. move/orP in cond2. case:cond1 =>[tt1|ff1]. rewrite tt1. 
  case:cond2 =>[tt2|ff2]. by rewrite tt2. rewrite- eqbF_neg in ff2. move/eqP in ff2. by rewrite ff2. 
  rewrite- eqbF_neg in ff1. move/eqP in ff1. rewrite ff1. 
  case:cond2 =>[tt2|ff2]. by rewrite tt2. rewrite- eqbF_neg in ff2. move/eqP in ff2. by rewrite ff2.   
Qed.

Lemma eq_contrapos: forall b1 b2:bool, (b1 == b2) = (~~b1 == ~~b2). 
Proof.
  move=> b1 b2.
  have cond1: b1 || ~~b1. apply orbN. have cond2: b2 || ~~b2. apply orbN.
  move/orP in cond1. move/orP in cond2. case:cond1 =>[tt1|ff1]. rewrite tt1. 
  case:cond2 =>[tt2|ff2]. by rewrite tt2. rewrite- eqbF_neg in ff2. move/eqP in ff2. by rewrite ff2. 
  rewrite- eqbF_neg in ff1. move/eqP in ff1. rewrite ff1. 
  case:cond2 =>[tt2|ff2]. by rewrite tt2. rewrite- eqbF_neg in ff2. move/eqP in ff2. by rewrite ff2.   
Qed.

Definition eq_dual_or := Bool.negb_orb. 
Definition eq_dual_and := Bool.negb_andb. 
Definition eq_dual_le := ltnNge. 
Definition eq_comm_plus := addnC.
Definition eq_assoc_plus := addnA. 
Definition eq_le_eq_lt := leq_eqVlt.
Definition eq_mono_plus_lt_plus := ltn_add2r.
Definition eq_mono_plus_le_plus := leq_add2r. 

Lemma iff_not_eq: forall b1 b2: bool, (~~b1 == b2) <-> (b1 == ~~b2).
Proof.
  move => b1 b2. split. 
  move => H. move/eqP in H. rewrite- H. by rewrite Bool.negb_involutive. 
  move => H. move/eqP in H. rewrite H. by rewrite Bool.negb_involutive. 
Qed.

Lemma eq_not_eq: forall b1 b2: bool, (~~b1 == b2) = (b1 == ~~b2).
Proof.
  move=> b1 b2. apply/conv_iff_eql. apply iff_not_eq. 
Qed.

Lemma eq_dual_lt: forall m n : nat, ~~ (m < n) = (n <= m). 
Proof.
  move => m n. rewrite eq_dual_le. by rewrite Bool.negb_involutive. 
Qed.

(* --- Properties about equality --- *)
Lemma eq_zero_plus_r: forall m n : nat, (m == 0) = (m+n == n). 
Proof.
  move=> m n. rewrite- {2} (add0n n). symmetry. apply (eqn_add2r n m 0). 
Qed. 

Lemma eq_zero_plus_l: forall m n : nat, (m == 0) = (n+m == n). 
Proof.
  move=> m n. rewrite- {2} (addn0 n). symmetry. apply (eqn_add2l n m 0). 
Qed. 

Lemma eq_mono_succ_eq: forall m n : nat, (m == n) = (m.+1 == n.+1). 
Proof.
  move=> m n. rewrite- (addn1 m). rewrite- (addn1 n). symmetry. apply eqn_add2r.
Qed. 

(* --- Properties about inequalities --- *)
Lemma eq_le_pred_eq_zero: forall n : nat, (n <= n.-1) = (n==0).
Proof.
  move => n. apply/conv_bool_eq. rewrite eq_contrapos. rewrite- ltnNge.
  rewrite ltn_predL. apply/eqP. by rewrite lt0n.     
Qed.

Lemma eq_mono_succ_le: forall m n : nat, (m <= n) = (m.+1 <= n.+1). 
Proof.
  move=> m n. rewrite- (addn1 m). rewrite- (addn1 n). symmetry. apply eq_mono_plus_le_plus.
Qed. 

Lemma eq_mono_succ_lt: forall m n : nat, (m < n) = (m.+1 < n.+1). 
Proof.
  move=> m n. rewrite- {2} (addn1 m). rewrite- (addn1 n). symmetry. apply eq_mono_plus_lt_plus. 
Qed. 

Lemma eq_lt_plus_r: forall m n : nat, (0 < n) = (m < n+m). 
Proof.
  move=>m n. rewrite- {1} (add0n m). by rewrite ltn_add2r. 
Qed.

Lemma eq_lt_plus_l: forall m n : nat, (0 < n) = (m < m+n). 
Proof.
  move=> m n. rewrite addnC. by apply eq_lt_plus_r. 
Qed.

Lemma eq_le_plus_r: forall m n : nat, (0 <= n) = (m <= n+m). 
Proof.
  move=> m n. rewrite- {1} (add0n m). by rewrite leq_add2r. 
Qed.

Lemma eq_le_plus_l : forall m n : nat, (0 <= n) = (m <= m+n). 
Proof.
  move=> m n. rewrite addnC. by apply eq_le_plus_r.   
Qed.

Lemma eq_S_le_add_r: forall m n : nat, (0 < n) = (m.+1 <= n+m). 
Proof.
  move=> m n. rewrite- {1} (add0n m). by rewrite ltn_add2r.
Qed.

(* transitivity *)
Definition trans_lelele := leq_trans.
Definition trans_ltltlt := ltn_trans.
Definition trans_leltlt := leq_ltn_trans.

Lemma trans_ltlelt: forall p m n : nat, m < p -> p <= n -> m < n.
Proof.
  move => n m k A B.
  rewrite eq_le_eq_lt in B. move /orP in B.
  move : B. move => [B1|B2]. 
  move /eqP in B1. by rewrite- B1.
  apply (trans_ltltlt A B2).
Qed.

(* Adjointnesses of plus and minus *)
Definition eq_adjoint_minus_plus_lt' := ltn_subLR. 

Lemma eq_adjoint_minus_plus_lt: forall p m n: nat, p <= m -> (m-p < n) = (m < n+p).
Proof.
  move=> p m n. rewrite (addnC n p). by apply eq_adjoint_minus_plus_lt'. 
Qed.

Lemma eq_adjoint_plus_minus_lt: forall p m n: nat, (m+p < n) = (m < n-p).
Proof.
  move=> p m n. rewrite ltn_subRL. by rewrite addnC. 
Qed.   

Lemma eq_adjoint_plus_minus_lt': forall p m n: nat, (p+m < n) = (m < n-p).
Proof.
  move=> p m n. rewrite (addnC p m). by apply eq_adjoint_plus_minus_lt. 
Qed.

Lemma eq_adjoint_plus_minus_le: forall p m n: nat, p <= n -> (m+p <= n) = (m <= n-p).
Proof.
  move=> p m n A. rewrite- (Bool.negb_involutive (m + p <= n)). rewrite- (Bool.negb_involutive (m <= n-p)). 
  rewrite- !eq_dual_le. rewrite- (subSn A). by rewrite- eq_adjoint_plus_minus_lt.  
Qed.

Lemma eq_adjoint_plus_minus_le': forall p m n: nat, p <= n -> (p+m <= n) = (m <= n-p).
Proof.
  move=> p m n. rewrite (addnC p m). by apply eq_adjoint_plus_minus_le.
Qed.

Lemma eq_adjoint_minus_plus_le: forall p m n: nat, (m-p <= n) = (m <= n+p).
Proof.
  move=> p m n. rewrite- (Bool.negb_involutive (m - p <= n)). rewrite- (Bool.negb_involutive (m <= n+p)).
  rewrite- eq_dual_le. rewrite- eq_adjoint_plus_minus_lt. by rewrite eq_dual_le.
Qed.

Lemma eq_adjoint_minus_plus_le': forall p m n: nat, (m-p <= n) = (m <= p+n).
Proof.
  move=> p m n. rewrite (addnC p n). by apply eq_adjoint_minus_plus_le.
Qed.

Lemma eq_adjoint_P_S_lt: forall m n: nat, 0 < m -> (m.-1 < n) = (m < n.+1).
Proof.
  move=> m n. rewrite- (addn1 n). rewrite- subn1. apply eq_adjoint_minus_plus_lt. 
Qed.

Lemma eq_adjoint_P_S_le: forall m n: nat, (m.-1 <= n) = (m <= n.+1).
Proof.
  move=> m n. rewrite- (addn1 n). rewrite- subn1. apply eq_adjoint_minus_plus_le. 
Qed.

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
  rewrite !eqn_leq. rewrite A. rewrite B. done. 
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
  rewrite !eqn_leq. rewrite A. rewrite B. done. 
Qed.

Lemma eq_adjoint_P_S_eq: forall m n: nat, 0 < m -> (m.-1 == n) = (m == n.+1).
Proof.
  move=> m n H. symmetry. rewrite eq_sym. rewrite (eq_sym (m.-1) n). by apply eq_adjoint_S_P_eq. 
Qed.  

(* odd and even *)
(*
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
  simpl. by rewrite Bool.negb_involutive.
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
 *)

Lemma eq_even_plus: forall m n: nat, ~~ssrnat.odd m -> ssrnat.odd (m+n) = ssrnat.odd n.
Proof.
  move=> m n H. rewrite oddD. apply negbTE in H. rewrite H. done. 
Qed. 
  
Lemma eq_odd_plus: forall m n: nat, ssrnat.odd m -> ssrnat.odd (m+n) = ~~ssrnat.odd n.
Proof.
  move=> m n H. rewrite oddD. rewrite H. done. 
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
  have A: (((m./2).*2)+(ssrnat.odd m) = m). rewrite addnC. apply odd_double_half.
  rewrite- {2} A. rewrite- addn1. apply/eqP. rewrite eqn_add2l. by rewrite odd.
Qed.

Lemma eq_double_half: forall m: nat, (m.*2)./2 = m. 
Proof.
  move=>m. have H: (m.*2)./2 = 0+m. apply (half_bit_double m false). by rewrite add0n in H. 
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
  rewrite A. rewrite B. done. by rewrite !eqn_leq. 
Qed.

Lemma eq_mono_double_lt: forall m n: nat, (m < n) = (m.*2 < n.*2).
Proof.
  move=> m n. rewrite !eq_dual_le. by rewrite eq_mono_double_le.
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
  - have evenM: ~~ssrnat.odd m. rewrite- eqbF_neg in evenN. move/eqP in evenN. rewrite evenN in H.
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
  rewrite eqn_leq. rewrite A. rewrite B. by rewrite eqn_leq.
Qed.

Lemma imp_mono_half_lt: forall m n: nat, (ssrnat.odd n <= ssrnat.odd m) -> (m < n) = (m./2 < n./2).
Proof.
  move=> m n H. rewrite !eq_dual_le. by rewrite eq_mono_half_le. 
Qed.

(* Adjointnesses of double and half *)
Lemma eq_adjoint_double_half_le: forall m n: nat, (m.*2 <= n) = (m <= n./2).
Proof.
  move=> m n.
  have condN: ssrnat.odd n || ~~ssrnat.odd n. apply orbN. move:condN. case/orP =>[oddN|evenN].
  rewrite eq_mono_half_le. by rewrite eq_double_half. rewrite oddN. apply le_bool_true. 
  rewrite eq_mono_half_le. by rewrite eq_double_half. rewrite- eqbF_neg in evenN.
  move/eqP in evenN. rewrite evenN. by rewrite odd_double.
Qed. 

Lemma eq_adjoint_half_double_le: forall m n: nat, ~~(ssrnat.odd m) -> (m./2 <= n) = (m <= n.*2).
Proof.
  move=> m n evenM.
  have evenN2: ~~ssrnat.odd (n.*2). by rewrite odd_double.
  have cond: ssrnat.odd m <= ssrnat.odd (n.*2).
  rewrite- eqbF_neg in evenM. move/eqP in evenM. rewrite evenM.
  rewrite- eqbF_neg in evenN2. move/eqP in evenN2. rewrite evenN2. done. 
  rewrite (eq_mono_half_le cond). by rewrite eq_double_half. 
Qed.  
  
Lemma eq_adjoint_double_half_lt: forall m n: nat, ~~(ssrnat.odd n) -> (m.*2 < n) = (m < n./2).
  move=> m n evenN. have A: ~~(m < n./2) = ~~(m.*2 < n).
  rewrite !eq_dual_lt. by rewrite eq_adjoint_half_double_le. 
  rewrite- (Bool.negb_involutive (m.*2 < n)). rewrite- (Bool.negb_involutive (m < n./2)).
  by rewrite A. 
Qed.

Lemma eq_adjoint_half_double_lt: forall m n: nat, (m./2 < n) = (m < n.*2).
Proof.
  move=> m n. have A: ~~(m < n.*2) = ~~(m./2 < n).
  rewrite !eq_dual_lt. by rewrite eq_adjoint_double_half_le. 
  rewrite- (Bool.negb_involutive (m./2 < n)). rewrite- (Bool.negb_involutive (m < n.*2)).
  by rewrite A. 
Qed.

Lemma eq_adjoint_double_half_eq: forall m n: nat, ~~(ssrnat.odd n) -> (m.*2 == n) = (m == n./2).
  move=> m n H. 
  have A: (m.*2 <= n) = (m <= n./2). by rewrite eq_adjoint_double_half_le. 
  have B: (n <= m.*2) = (n./2 <= m). by rewrite eq_adjoint_half_double_le.
  rewrite !eqn_leq. rewrite A. by rewrite B.
Qed.

Lemma eq_adjoint_half_double_eq: forall m n: nat, ~~(ssrnat.odd m) -> (m./2 == n) = (m == n.*2).
Proof.
  move=> m n H. 
  have A: (m./2 <= n) = (m <= n.*2). by rewrite eq_adjoint_half_double_le. 
  have B: (n <= m./2) = (n.*2 <= m). by rewrite eq_adjoint_double_half_le.
  rewrite !eqn_leq. rewrite A. by rewrite B.
Qed.

Lemma self_double: forall n:nat, n <= n.*2.
Proof.
  move=>n. rewrite- addnn. by rewrite-  eq_le_plus_r.
Qed.

Lemma self_half: forall n:nat, n./2 <= n.
Proof.
  move=>n. rewrite- {2} (half_bit_double n false). simpl. rewrite add0n. 
  apply imp_mono_half_le. apply self_double. 
Qed.

