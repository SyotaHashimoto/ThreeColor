From mathcomp
     Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import Even Coq.Arith.Le Coq.Arith.Lt Coq.Arith.Plus.
Require Import Lia.

Notation "x .^ y" :=  (expn x y)%coq_nat (at level 30, right associativity).

Lemma coqnat_lt: forall m n : nat, m < n <-> (m < n)%coq_nat.
Proof.
  move=> m n.
  split.
  apply/ltP.
  move /ltP. by [].
Qed.

Lemma coqnat_gt: forall m n : nat, m > n <-> (m > n)%coq_nat.
Proof.
  move=> m n.
  split.
  apply/ltP.
  move /ltP. by [].
Qed.

Lemma coqnat_le: forall m n : nat, m <= n <-> (m <= n)%coq_nat.
Proof.
  move=> m n.
  split.
  apply/leP.
  move /leP. by [].
Qed.

Lemma coqnat_ge: forall m n : nat, m >= n <-> (m >= n)%coq_nat.
Proof.
  move=> m n.
  split.
  apply/leP.
  move /leP. by [].
Qed.


Lemma coqnat_eq: forall m n : nat, m = n <-> (m = n)%coq_nat.
Proof.
  move=> m n. by[].
Qed.

Lemma coqnat_plus: forall m n : nat, m + n = (m + n)%coq_nat.
Proof.
  move=> m n. by[].
Qed.

Lemma coqnat_minus: forall m n : nat, m - n = (m - n)%coq_nat.
Proof.
  move=> m n. by[].
Qed.

Lemma coqnat_mult: forall m n : nat, m * n = (m * n)%coq_nat.
Proof.
  move=> m n. by[].
Qed.

(* expn m n = (expn m n)%coq_nat *)
Lemma coqnat_expn: forall m n : nat, m ^ n = (m .^ n)%coq_nat.
Proof.
  move=> m n. by [].
Qed.
