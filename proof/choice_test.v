Require Import PeanoNat Le Lt Plus Mult Even.
From mathcomp
     Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import Classical_Prop.
Require Import Psatz.
Require Import CoqNat MyRewrite.

Require Import Coq.Logic.ClassicalUniqueChoice.

Variable P :  nat -> nat -> Prop.

Hypothesis P_exists : forall P:nat->nat->Prop, forall x : nat, (exists z : nat, P x z).

Hypothesis P_uniq : forall P:nat->nat->Prop, forall x: nat, forall z0 z1 : nat, (P x z0 /\ P x z1) -> z0 = z1.

Hypothesis P_mix : forall P:nat->nat->Prop, forall x: nat, forall z0 z1: nat, P x z0 /\ P (x.+1) z1 -> z1 = z0+3.
(* 
P_exists と P_uniq より各 i について P i ai となる ai は1つだけ存在する．
P_mix より a1=a0+3，a2=a1+3,...,a(i+1)=ai+3 なので，P n z は z = 3*n + a0 を定めている
a0 を何にするかが不確定だが，これさえ与えれば全て確定する (Cpos の場合は最上段だが，それの簡易版)
つまり，a0 を与えることが最上段の色の塗り方を与えることに相当する．
*)

Lemma P_property: forall P:nat->nat->Prop, forall a0 x:nat, P 0 a0 -> P x (3*x + a0). (* 上記の説明から得られる性質 *)
Proof.
  move=>a0 x P0.
  induction x. done. 
  have A: 3*x.+1 + a0 = 3*x + a0 + 3.
  rewrite mulnSr. rewrite eq_assoc_plus. rewrite (eq_comm_plus 3 a0). rewrite eq_assoc_plus. done.
  have B: exists z1:nat, P x.+1 z1. by apply P_exists. move:B. case=> z1 B.
  have C: z1 = 3*x+a0+3. apply (P_mix x). split. done. done. rewrite A. rewrite- C. done. 
Qed.

Definition TriA P x z0 z1 n := P x z0 /\ P (x+n) z1 -> exists k:nat, z1 = z0 + 5*k.
(*
「P x z0 と P (x+n) z1 のとき z0 と z1 の差が5の倍数だ」
これは上の話から z1-z0 = 3*n なので n が 5の倍数であることと同値 (3と5が互いに素なので)  
つまり， forall x z0 z1, (n = 5*? <-> TriP x z0 z1 n) がいえるはず．
これが三角形三色問題の簡易版
*)  

Hypothesis myLemma: forall x n: nat,  ~(exists k:nat, n = 5*k) -> ~(forall a0:nat, forall P: nat->nat->Prop, TriA P x (3*x + a0) (3*(x+n)+a0) n).
(* 
証明に突入しないように Hypothesis としているが，本当は示すべき補題 (下で示す)．
これが Three_Color_Triangle_Problem_nec' や Three_Color_Triangle_Problem_nec_XX などの簡易版
a0 の存在を示したいのだが，そのためには P 0 a0 を満たす a0 を取ってくればよい．
問題はこの a0 を Coq でどうやって取ってくるか．これを与えるのが unique_choice
*)
Check unique_choice.

Lemma get_a0_without_choice: exists! a:nat, P 0 a. (* いまの簡易版だと unique_choice は不要．一意存在の練習もする *)
Proof.
  (* exists! は https://coq.inria.fr/distrib/current/stdlib/Coq.Init.Logic.html に定義されている *)
  (* ex! x.P(x) は ex x.(P(x) /\ all y.(P(y) -> x=y)) の略記 (存在し，さらに一意) *)
  (* Coq で処理するにはまず， unique_existence を使ってバラす *)
  apply/unique_existence. split.
  - by apply P_exists. (* 存在性 *)
  - rewrite /uniqueness. (* 一意性 *)
    move=>x y Hx H1. by apply (P_uniq 0).
Qed.

Lemma get_a0_with_choice: exists a:nat, P 0 a. (* unique_choice を使った証明 *)
Proof.
  have exF: exists f:nat->nat,forall x:nat,P x (f x).
  apply unique_choice.
  move=> x. apply/unique_existence. split. 
  - by apply P_exists. (* 存在性 *)
  - rewrite /uniqueness. move=>x0 y Hx H1. by apply (P_uniq x). (* 一意性 *)
  move:exF. case=>f x. exists (f 0). done. 
Qed.

(* これは単なるショートカット．両辺を変形すると 3b = 5*k となり，3と5が互いに素なので b は5の倍数 *)
Lemma shortcut: forall a b c k: nat, 3 * (a + b) + c = 3 * a + c + 5 * k -> exists q:nat, b = 5*q. 
Admitted. 

(* 上の myLemma を示す *)
Lemma myLem: forall(x n: nat),  ~(exists k:nat, n = 5*k) -> ~(forall a0:nat, forall P:nat->nat->Prop, TriP x (3*x + a0) (3*(x+n)+a0) n).
Proof.
  move=>x n H Tri.
  have exA: exists a:nat, P 0 a. apply get_a0_with_choice.
  move:exA. case=>a0 P0a.
  have TriA0: TriP x (3 * x + a0) (3 * (x + n) + a0) n. by apply Tri. 
  have five: exists k:nat,(3*(x+n)+a0)=(3*x+a0) + 5*k. apply TriA0. 
  split. by apply P_property. by apply P_property.
  have n_is_0_mod_5: exists k:nat, n = 5*k. 
  move:five. case=>k H1. by apply (shortcut x n a0 k). contradiction. 
Qed.


