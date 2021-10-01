Require Import PeanoNat Le Lt Plus Mult Even.
From mathcomp
     Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import CoqNat MyRewrite.

Notation "x .^ y" :=  (expn x y)%coq_nat (at level 30, right associativity).

(*------------------------------------
ver6 の方針
- 関数 cpos を基にした形式化
- Import は減らす
- CoqNat は廃止, MyRewrite は可能な限り減らす
- できるだけ boolにする
-- 対偶の処理を楽にするため
-- Classical を除ける
-- TriangleF は bool として定義した
-- F_mix は bool にはできなそう
-- WellColoredTriangleF は F_mix を含むので bool にできなそう
-------------------------------------*)

(*
述語はやめる．関数で書けるならそっちの方がよい．
紙に証明を書いてから実装するべし
ssreflect 流で Prop でなく bool を使うべし

*)

(*
ssrnatライブラリを使えば、proof_coq.vは簡潔かつ本質的な部分のみにフォー
カスできるようになります。
特にCoqNat, %coq_natのscopeは不要だと思われます。
--> 対処予定

直接expnやssrnatを使うと、証明は短くなります。例えば：
Lemma leq23m_3m1 n m : n <= 2 * 3 ^ m -> n < 3 ^ m.+1.
Proof.
move=> ?.
by rewrite expnS -{1}(addn1 2) mulnDl mul1n -(addn1 n) leq_add //
expn_gt0.
Qed.
Lemma leqn_n1 n m : 3 ^ m <= n -> 3 ^ m <= n.+1.
Proof. by move/leq_trans; apply. Qed.
Lemma leqNatOr : forall (n m : nat), (n <= m) \/ (m + 1 <= n).
Proof. by move => n m; apply/orP; rewrite addn1; case: leqP. Qed.
などなど。これらの証明は短くなるので，補題として切り出す必要がなくなる
と思われます．
例えば、leqNatOrを使うときに、leqPを直接使ったほうがいいでしょう。
(ちなみに、natで0 <= nはいつもtrueです。)
同様にMyRewrite.vもssrboolやssrnatに既にある補題を証明しているように
見えます。
--> hashimoto

Propの代わりに、boolを使えませんか？
すると、Section Classicalはいらなくなります。
Contrapositionの代わりにcontra補題(ssrbool)を使えます。
ssrboolをもう少し有利に使えます。
(... == falseの代わりに、~~ ...を書く；
Bool.andb_true_r -> andbT,
Bool.orb_true_iffの代わりに, orPを使う,
odd_or_even -> oddはboolなのでcaseで一発証明できます)
--> 努力する

通常、Coqの証明にAxiomをできるだけ避けます。
Axiomを使わずに、Cposを定義できませんか？
--> 関数 cpos に変更したので Axiom も消滅した

(apply conj -> split)
--> finish
*)

Section nat1.

  (* --- 加法の性質 --- *)
(*  
  Lemma add3 : 3 = 2 + 1.
  Proof. by rewrite /=. Qed.
*)
  (* --- 減法の性質 --- *)
  
  Lemma x_minus_x_is_0 : forall x : nat, x - x = 0.
  Proof. elim=> [ | x IHx]; by []. Qed.

  Lemma x_plus_y_minus_x_is_y: forall x y : nat, x + y - x = y.
  Proof.
    move=> x y.
    have G1: x + y = y + x. apply Nat.add_comm.
    rewrite G1. rewrite- addnBA.
    have G2: (x-x)%coq_nat = 0.
    apply Nat.sub_diag. rewrite- coqnat_minus in G2. rewrite G2.
    apply Nat.add_0_r. apply coqnat_le, le_n.
  Qed.

  (* --- 乗法の性質 --- *)
  
  Lemma mulnDr' :
    forall m n p : nat, (m + n) * p = m * p + n * p.
  Proof.
    move=> m n.
    elim=> [ | p IHp].
    - by rewrite 3!muln0.
    - rewrite mulnC.
      rewrite [m * p.+1]mulnC; rewrite [n*p.+1]mulnC. by apply mulnDr.
  Qed.
  
  (* --- 指数の性質 --- *)
  
  Lemma add3n3n :
    forall n : nat, (3 .^ n) + (3 .^ n) = 2 * (3 .^ n).
  Proof. case=> [ | n]. by []. by rewrite addnn mul2n. Qed.
  
  Lemma add23n3n :
    forall n : nat, (3 .^ n).*2 + (3 .^ n) = 3 .^ (n.+1).
  Proof. 
    move=> n.
    rewrite- mul2n. rewrite- {2}[3.^n]mul1n mulnC. rewrite [1*3.^n]mulnC. rewrite- mulnDr.
    have Three : 2 + 1 = 3. by [].
    rewrite Three. by rewrite expnS mulnC.
  Qed.
  
  Lemma expnPos: forall n m : nat, 0 < n -> 0 < n .^ m.
  Proof.
    move=> n m. rewrite expn_gt0.
    move=> pos_n. apply/orP. by left.
  Qed.

  Lemma expn3neq0 : forall m, 3.^m != 0.
  Proof. move=> m. rewrite- lt0n. by apply expnPos. Qed.

  Lemma expn3Pos : forall m, 0 < 3.^m .
  Proof. move=> m. by apply expnPos. Qed.

  (* ---  不等式の性質 -- *)
  
  Lemma leq23m_3m1 :
    forall (n m : nat), (n <= (3 .^ m).*2) -> (n < 3 .^ m.+1).
  Proof.
    move=> n m H.
    have A: 0 < 3.^m. by apply expn3Pos.
    have B: 2<3. done. 
    have two_M_le_three_M : 2 * 3 .^ m < 3 * 3 .^ m. rewrite ltn_mul2r. rewrite A. rewrite B. done. 
    rewrite- add23n3n. apply (trans_leltlt H). rewrite- eq_S_le_add_l. by apply expn3Pos.
  Qed.
  
  Lemma leq3m_23m1 :
    forall (n m : nat), ((3 .^ m).*2 + 1 <= n) -> (3 .^ m <= n).
  Proof.
    move=> n m.
    suff : (3 .^ m <= (3 .^ m).*2 + 1).
    move=> tmp1 tmp2. apply coqnat_le.
    apply (PeanoNat.Nat.le_trans (3 .^ m) ((3 .^ m).*2 + 1) n).
    apply coqnat_le. by []. by apply coqnat_le. 
    rewrite- addnn. apply coqnat_le.
    rewrite (_ : 3 .^ m + 3 .^ m + 1 = (3 .^ m + (3 .^ m + 1))%coq_nat).
    apply PeanoNat.Nat.le_add_r. by rewrite- plus_assoc_reverse.            
  Qed.
  
  Lemma leqn_n1 :
    forall (n m : nat), 3 .^ m <= n -> 3 .^ m <= n.+1.
  Proof.
    move=> n m H.
    suff H1: n < n.+1.
    have P : (3.^m < n.+1)%coq_nat.
    apply (PeanoNat.Nat.le_lt_trans (3 .^ m) n (n.+1)).
    apply coqnat_le. by[]. by apply coqnat_le.
    apply coqnat_le; by apply PeanoNat.Nat.lt_le_incl. by []. 
  Qed.

  Lemma leq_false1 : forall n i : nat, n./2.+1 <= i <= n -> (0 <= i <= n./2 = false).
  Proof.
    move=> n i.
    move /andP. move=> [] range1 range2. rewrite /=. by apply ltn_geF.
  Qed.

  Lemma leq_false2 : forall n i : nat, 0 <= i <= n./2 -> (n./2.+1 <= i <= n = false).
  Proof.
    move=> n i.
    move /andP. move=> [] range1 range2.
    apply /andP. apply /andP. rewrite negb_and.
    apply /orP. left. by rewrite- leqNgt.
  Qed.
  
  (* --- odd に関する性質 --- *)

  Lemma oddS n : odd n.+1 = ~~ odd n.
  Proof. done. Qed.

  Lemma oddD m n : odd (m + n) = odd m (+) odd n.
  Proof. by elim: m => [|m IHn] //=; rewrite -addTb IHn addbA addTb. Qed.
  
  Lemma oddM m n : odd (m * n) = odd m && odd n.
  Proof. by elim: m => //= m IHm; rewrite oddD -addTb andb_addl -IHm. Qed.
  
  Lemma oddexpn : forall n m : nat, odd m -> odd (m.^n).
  Proof.
    move=> n. 
    elim n. by []. move=> k ind m. 
    rewrite expnS. rewrite oddM. move=>odd. apply/andP. split. by [].
    rewrite ind. by []. by [].
  Qed.

  Lemma odd3m : forall m : nat, odd (3.^m).
  Proof. move=> m. by apply oddexpn. Qed.

  (* --- 場合分けに関する補題 --- *)
  
  Lemma case1 : forall n : nat, n.+1 = 1 \/ n.+1 > 1.
  Proof.
    elim=> [ | n IHn].
    - left. by[].
    - case IHn => H0.
      + rewrite H0. by right.
      + right. apply /ltP; apply le_S; by apply /ltP.
  Qed.

  Lemma leqNatOr:
    forall (n m : nat), (n <= m) \/ (m + 1 <= n).
  Proof.
    move=> n m.
    have le_sum_gt: {(n <= m)%coq_nat} + {(m.+1 <= n)%coq_nat}.
    apply Compare_dec.le_le_S_dec.
    case le_sum_gt => [le|gt].
    - left. by apply coqnat_le.
    - right. rewrite (_: (m+1)= (m.+1)). by apply coqnat_le. by apply addn1.
  Qed.
  
  Lemma leq23mOr :
    forall (n m : nat), (n <= 2 * 3 .^ m) \/ (2 * 3 .^ m + 1 <= n).
  Proof. by move=> n m; apply leqNatOr. Qed.
  
  Lemma odd_or_even : forall n : nat, odd n \/ odd n = false.
  Proof.
    elim=> [ | n IHn].
    - right. done.
    - case IHn => [Odd|Even].
      + right. by rewrite oddS Odd.
      + left.  by rewrite oddS Even.
  Qed.

  (* 不等式の書き換えに用いる補題 *)
  
  Lemma  Short1 :
    forall n k : nat, 3 .^ k <= n <= (3 .^ k).*2 <-> (3 .^ k <= n /\ n <= 2 * (3 .^ k)).
  Proof.
    move=> n k. split.
    move=> H. apply /andP. by rewrite mul2n.
    move=> H. apply /andP. by rewrite mul2n in H.
  Qed.

  Lemma Long1 :
    forall n k : nat, (3 .^ k).*2 + 1 <= n < 3 .^ k.+1 <-> 2 * (3 .^ k) + 1 <= n /\ n < 3 .^ k.+1.
  Proof.
    move=> n k. split.
    move=> H. apply /andP. by rewrite mul2n.
    move=> H. apply /andP. by rewrite mul2n in H.
  Qed.
  
  Lemma Short2 :
    forall n k : nat, 3 .^ k <= n.+1 <= (3 .^ k).*2 <-> (3 .^ k <= n.+1 /\ n.+1 <= 2 * (3 .^ k)).
  Proof.
    move=> n k. split.
    move=> H. apply /andP. by rewrite mul2n.
    move=> H. apply /andP. by rewrite mul2n in H.
  Qed.

  Lemma Long2 :
    forall n k : nat, (3 .^ k).*2 + 1 <= n.+1 < 3 .^ k.+1 <-> 2 * (3 .^ k) + 1 <= n.+1 /\ n.+1 < 3 .^ k.+1.
  Proof.
    move=> n k. split.
    move=> H. apply /andP. by rewrite mul2n.
    move=> H. apply /andP. by rewrite mul2n in H.
  Qed.

  Lemma  Boundary :
    forall n k : nat, (n.+1 = 3 .^ k.+1) <-> (n.+1 == 3 .^ k.+1).
  Proof. move=> n k. split => H. by apply /eqP. by apply /eqP. Qed.

  Lemma connect3m :
    forall n m : nat,
      (3 .^ m <= n /\ n <= (3 .^ m).*2) \/ ((3 .^ m).*2 + 1 <= n /\ n < 3 .^ m.+1) <->
      (3 .^ m <= n /\ n < 3 .^ m.+1).
  Proof.
    move=> n m. split.
    - move=> Long; case Long.
      + move=> []Left1 Left2; split. done. by apply leq23m_3m1.
      + move=> [] Right1 Right2; split. apply leq3m_23m1. done. by [].
    - move=> [] Short1 Short2.
      have leq23mOr : forall m1 m2 : nat, (n <= (3.^m).*2) \/ ((3.^ m).*2 + 1 <= n).
      move=> m1 m2; by apply leqNatOr.
      case (leq23mOr n m) => [Less|More].
      + left.  split. by []. by [].
      + right. split. by []. by [].
  Qed.
 
End nat1.

(* Ver6 でここは削除
Section Classical.

  Definition Lem : Prop := forall P : Prop, P \/ ~P.
  Definition Dne : Prop := forall P : Prop, ~(~P) -> P.

  (* 排中律 と 二重否定除去 が同値であることを示す *)
  
  Lemma Lem_iff_Dne : Lem <-> Dne.
  Proof.
    rewrite /Lem /Dne. split.
    - move=> Lem P.
      have : P \/ ~P. by apply Lem.
      rewrite /not. by case.
    - move=> Dne P.
      apply Dne => nLem.
      apply nLem. right => PisTrue.
      apply nLem; by left.
  Qed.

  (* 古典論理において任意の命題とその命題の対偶が同値であることを示す *)
  Lemma Contraposition : forall P Q : Prop, (P -> Q) <-> (~Q -> ~P).
  Proof.
    move=> P Q; split.
    - move=> PtoQ nQ QisTrue.
      apply nQ; by apply PtoQ.
    - move=> nQtonP PisTrue.
      apply imply_to_or in nQtonP.
      case nQtonP.
      + by apply NNPP.
      + by [].
  Qed.
  
End Classical.
 *)

Section Three_Color_Triangle_Problem.

  (* --- 定義一覧 --- *)
  Inductive Color : Set :=
  | red
  | yel
  | blu.
  (*三角形三色問題で用いる色の集合 Color を定義 *)
  (* 用いる色は次の3色 red:red, yel:yellow, blu:blue のつもり*) 

  (* ここから Ver6 *)  
  Definition eqcol c0 c1 :=
    match c0,c1 with
    | red,red => true
    | blu,blu => true
    | yel,yel => true
    | _,_ => false
    end.

  Notation "c1 === c2" :=  (eqcol c1 c2) (at level 30, right associativity).

  Lemma ceqP:  forall c0 c1: Color, reflect (c0 = c1) (c0 === c1).
  Proof.
    move=>c0 c1.    
    case c0,c1; do ! [ by apply Bool.ReflectT | by apply Bool.ReflectF ].
  Qed.
  
  Definition mix (c0 c1 : Color) : Color :=
    match c0, c1 with
    | red, red => red
    | red, yel => blu
    | red, blu => yel
    | yel, red => blu
    | yel, yel => yel
    | yel, blu => red
    | blu, red => yel
    | blu, yel => red
    | blu, blu => blu
    end.
  (* 2色を用いて次の段に塗る色を決める演算 mix を定義 *)
  
  Definition F_mix (cpos:nat->nat->Color) := forall x y:nat, (cpos x (y.+1)) === mix (cpos x y) (cpos (x.+1) y).
  
  (* (x,y) (x+n,y) (x,y+n) の3頂点の色が mix になっている *)
  Definition TriangleF cpos x y n : bool := (cpos x (y+n)) === mix (cpos x y) (cpos (x+n) y). 

  (* (x,0) から始まる n 段の三角形に要請通りの任意の色塗りをしても 3頂点(x,0),(x+n,0),(x,n)の色は調和している *)
  Definition WellColoredTriangleF x n := forall cpos: nat->nat->Color, F_mix cpos -> TriangleF cpos x 0 n.
    
  (* ----- mix の性質 ----- *) 
  Lemma mixCom (c0 c1 : Color) : mix c0 c1 = mix c1 c0.
  Proof. case c0, c1; by rewrite /=. Qed.

  Lemma mixRight (c0 c1 c2: Color) :
    c2 = mix c0 c1 <-> c1 = mix c0 c2.
  Proof. case c0, c1, c2; do ! done. Qed.

  Lemma mixLeft (c0 c1 c2: Color) :
    c2 = mix c0 c1 <-> c0 = mix c1 c2.
  Proof. case c0, c1, c2; do ! done. Qed.
  
  Lemma mixCut (c0 c1 c2 c3 : Color) :
    mix ( mix (mix c0 c1) (mix c1 c2) ) ( mix (mix c1 c2) (mix c2 c3) ) = mix c0 c3.
  Proof. case c0, c1, c2, c3; by rewrite /=. Qed.

  (* ----- 三角形三色問題 ----- *)
  Lemma Three_Color_Triangle_Problem_suf' :
    forall cpos: nat->nat->Color, forall (k n x y : nat), 
        n = 3 .^ k
        -> F_mix cpos
        -> TriangleF cpos x y n. 
  Proof.
    move=>cpos k n x y H H_mix. 
    move: k n x y H. 
    elim=> [ | k IHk ].
    - move=> n x y Step.
      rewrite expn0 in Step. rewrite Step.
      rewrite /TriangleF. rewrite ! addn1. by apply H_mix.
    - move=> n x y Step.
      + have Triangle035 : TriangleF cpos x y (3.^k). by apply IHk.
      + have Triangle346 : TriangleF cpos (x+3.^k) y (3.^k). by apply IHk.
      + have Triangle417 : TriangleF cpos (x+(3.^k).*2) y (3.^k). by apply IHk.
      + have Triangle568 : TriangleF cpos x (y+3.^k) (3.^k). by apply IHk.
      + have Triangle679 : TriangleF cpos (x+3.^k) (y+3.^k) (3.^k). by apply IHk.
      + have Triangle892 : TriangleF cpos x (y+(3.^k).*2) (3.^k). by apply IHk.
      + rewrite /TriangleF.
        rewrite- (mixCut (cpos x y) (cpos (x+3.^k) y) (cpos (x+(3.^k).*2) y) (cpos (x+n) y)).
        rewrite /TriangleF in Triangle035.
        move:Triangle035; move/ceqP; move=>Triangle035; rewrite- Triangle035. 
        rewrite- !addnn. rewrite addnA.
        move:Triangle346; move/ceqP; move=>Triangle346; rewrite- Triangle346.
        move:Triangle568; move/ceqP; move=>Triangle568; rewrite- Triangle568.
        rewrite Step. rewrite- add23n3n. rewrite- ! addnA. rewrite addnn. rewrite! addnA. 
        move:Triangle417; move/ceqP; move=>Triangle417; rewrite- Triangle417.
        rewrite- addnn. rewrite! addnA. 
        move:Triangle679; move/ceqP; move=>Triangle679; rewrite- Triangle679.
        rewrite- !addnA. rewrite addnn. rewrite !addnA. 
        move:Triangle892; move/ceqP; move=>Triangle892; rewrite- Triangle892.
        rewrite- addnA. rewrite (addnC (3.^k) ((3.^k).*2)). rewrite !addnA.
        by apply/ceqP.
  Qed.

  Theorem Three_Color_Triangle_Problem_suf'' :
    forall (x y n : nat),
      (exists k : nat, n = 3 .^ k) ->
      forall cpos:nat->nat->Color, F_mix cpos -> TriangleF cpos x y n. 
  Proof.
    move=> x y n Step cpos H_mix. 
    move:Step. case; move=> k Step. 
    by apply (Three_Color_Triangle_Problem_suf' cpos k n x y).
  Qed.

  (* 十分条件 *)
  Theorem Three_Color_Triangle_Problem_suf :
    forall (x n : nat),
      (exists k : nat, n = 3 .^ k) -> (WellColoredTriangleF x n). 
  Proof.
    rewrite /WellColoredTriangleF.
    move=> x n Step cpos H_mix.  
    by apply Three_Color_Triangle_Problem_suf''.    
  Qed.

  (* ここから必要条件 *)
















  


  Lemma Three_Color_Triangle_Problem_nec_even :
    forall x n :nat, (n > 0) && (odd n == false) -> ~(WellColoredTriangleF x n).
  Admitted.
  (*
  Proof.
    move=> x n.
    move /andP; move=> [] NotZeroN OddN Triangle_hyp.
    have H_CposYB: exists Cpos' : nat -> nat -> Color -> Prop,C_uniq Cpos' /\ C_exists Cpos' /\ C_mix Cpos' /\ (forall x0 i : nat, Cpos' (x0 + i) 0 (colorYB x n (x0 + i))). 
    apply (C_paint' (colorYB x n)).
    move:H_CposYB.  case=> CposYB [H_uniq [H_exists [H_mix H]]].
    specialize (Triangle_hyp CposYB H_uniq H_exists H_mix).
    have topcolor : forall i : nat, ((0 <= i <= n) -> CposYB (x+i) 0 (colorYB x n (x+i))).
    move=>i range. apply H.       have ColorBelow : c = mix (colorYB x n x) (colorYB x n (x + n)).
      apply TriangleN. rewrite addn0 in Cpos0. done. done. done. split.
      rewrite eq_unit_plus_l in Cpos0. done. done. 
      
    (* CposY の色が yel であることを示す *)
    - have sameColor : colorYB x n x = colorYB x n (x + n).
      apply lemYB3; done. rewrite- sameColor in ColorBelow.
      have ColorY : colorYB x n x = yel.
      rewrite /colorYB. rewrite x_minus_x_is_0. by rewrite range0a.
      rewrite ColorY in ColorBelow. rewrite /= in ColorBelow.
      rewrite ColorBelow in CposY.

    (* falseColor より矛盾を示す *)
    - apply (falseColor CposYB x n red yel). apply H_uniq. 
      split. done. split. done. done.  
  Qed.
*)
  
  Lemma Three_Color_Triangle_Problem_nec_ShortOdd :
    forall x n k : nat, ((3.^k < n <= (3.^k).*2) && (odd n)) -> ~(WellColoredTriangleF x n).
  Admitted.
  (*
  Proof.
    - move=> x n k cond triangle.
      have H_CposYBBY: exists Cpos' : nat -> nat -> Color -> Prop,C_uniq Cpos' /\ C_exists Cpos' /\ C_mix Cpos' /\ (forall x0 i : nat, Cpos' (x0 + i) 0 (colorYBBY x n (x0 + i))). apply (C_paint' (colorYBBY x n)).
      move:H_CposYBBY; case=> [CposYBBY [H_uniq [H_exists [H_mix H]]]].
      specialize (triangle CposYBBY H_uniq H_exists).
      have topcolor : forall i : nat, ((0 <= i <= n) -> CposYBBY (x+i) 0 (colorYBBY x n (x+i))).
      move=>i range. apply H.       
      + move: (cond). move/andP. case=>[K1 K2].
      + have tri3k: forall x y: nat, forall c0 c1 c2: Color, Triangle CposYBBY x y (3.^k) c0 c1 c2.
        move=> x1 y1 c0 c1 c2. apply Three_Color_Triangle_Problem_suf''.
        exists k. done. done. done. 
      + have fromCpaint: forall i:nat,0<=i<=n -> CposYBBY (x+i) 0 (colorYBBY x n (x+i)).
        move=> i rangeI. done.
        
      + have fromOddC: CposYBBY x (0+n) red.
        apply (ShortOddC CposYBBY x n k). done. done. done. done. done. done. 
      + have A1: CposYBBY (x+0) 0 (colorYBBY x n (x+0)). apply fromCpaint. done. 
      + have A2: CposYBBY (x+n) 0 (colorYBBY x n (x+n)). apply fromCpaint.
        have B1: 0<=n. apply leq0n. have B2: n<=n. apply leqnn. rewrite B1. rewrite B2. done.
      + have [c' A3]: exists c':Color, CposYBBY x (0+n) c'. apply H_exists. 
      + have A4: Triangle CposYBBY x 0 n (colorYBBY x n x) (colorYBBY x n (x+n)) c'. apply triangle. done. rewrite addn0 in A1. done. done.
      + have mix1: c' = mix (colorYBBY x n x) (colorYBBY x n (x+n)). apply A4.
        split. rewrite- {1 3} (addn0 x). done. split. done. done. 
      + have A5: colorYBBY x n x = colorYBBY x n (x+n). apply lemYBBY5. done. 
      + have mix2: c' = mix (colorYBBY x n x) (colorYBBY x n x). rewrite {2} A5. done. 
      + have CposYel: CposYBBY x (0+n) (mix (colorYBBY x n x) (colorYBBY x n (x+n))). rewrite- mix1. done. 
      + have A6: colorYBBY x n x = yel. rewrite- {2} (addn0 x). apply lemYBBY1. done. 
      + have A7: c' = yel. rewrite A6 in mix2. done. 
      + have A8: CposYBBY x (0+n) yel. rewrite- A7. done. 
      + have A9: yel = red. apply (H_uniq x (0+n)). split. done. done. done. 
Qed.
*)
  
  (* 奇数の場合-2 終わり *)
  Lemma Three_Color_Triangle_Problem_nec_LongOdd :
  forall (x n k : nat), ((3.^k).*2 + 1 <= n < (3.^(k.+1))) -> ~(WellColoredTriangleF x n).
  Admitted.
(*
  Proof.
    - move=> x n k rangeN triangle.
      have H_CposBYB: exists Cpos' : nat -> nat -> Color -> Prop,C_uniq Cpos' /\ C_exists Cpos' /\ C_mix Cpos' /\ (forall x0 i : nat, Cpos' (x0 + i) 0 (colorBYB x n k (x0 + i))). apply (C_paint' (colorBYB x n k)).
      move:H_CposBYB.  case=> CposBYB [H_uniq [H_exists [H_mix H]]].
      specialize (triangle CposBYB H_uniq H_exists).
      have topcolor : forall i : nat, ((0 <= i <= n) -> CposBYB (x+i) 0 (colorBYB x n k (x+i))).
      move=>i range. apply H.       
      + move: (rangeN). move/andP. case=>[K1 K2].
      + have tri3k: forall x y: nat, forall c0 c1 c2: Color, Triangle CposBYB x y (3.^k) c0 c1 c2.
        move=> x1 y1 c0 c1 c2. apply Three_Color_Triangle_Problem_suf''.
        exists k. done. done. done. 
      + have fromCpaint: forall i:nat,0<=i<=n -> CposBYB (x+i) 0 (colorBYB x n k (x+i)).
        move=> i rangeI. done.
      
      + have A1: (3.^k) <= n. by apply fromRangeN.
      + have H_CposBYB: forall i:nat, 0<=i<=n -> CposBYB (x+i) 0 (colorBYB x n k (x+i)).
        move=> i rangeI. by apply fromCpaint. 
      + have CposR: CposBYB x n red. by apply (LongOddC CposBYB x n k).
      + have triBYB: Triangle CposBYB x 0 n (colorBYB x n k x) (colorBYB x n k (x+n)) red. apply triangle. done.
        rewrite- {1 3} (addn0 x).  by apply fromCpaint. done. done. 
      + have colB1: colorBYB x n k x = blu.
        rewrite- {2} (addn0 x). 
        apply (lemBYB1 x 0). done. 
      + have colB2: colorBYB x n k (x+n) = blu.
        apply (lemBYB3 x 0). apply/andP. split. 
        rewrite (eq_adjoint_minus_plus_lt n A1).
        rewrite- eq_lt_plus_l. apply expn3Pos. done. 
      + have triBBR: Triangle CposBYB x 0 n blu blu red.
        rewrite- {1} colB1. rewrite- {1} colB2. done.
      + have CposB1: CposBYB x 0 blu.
        rewrite- colB1. rewrite- {1 3} (addn0 x). apply H_CposBYB. done. 
      + have CposB2: CposBYB (x+n) 0 blu.
        rewrite- colB2. apply H_CposBYB. apply/andP. done. 
      + have mixRBB: red = mix blu blu.
        apply triBBR. split. done. done. done.         
  Qed.
 *)

  Theorem Three_Color_Triangle_Problem_nec :
    forall (n x : nat), n > 0 -> (WellColoredTriangleF x n) -> (exists k :nat, n = 3 .^ k).
  Admitted.
  (*
  Proof.
    rewrite /WellColoredTriangleF.
    move=> n x NotZeroN_hyp Notexp3k WCT.
    case (rangeN4 n) => k rangeN. case rangeN => [ZeroN|NotZeroN].
    - rewrite ZeroN in NotZeroN_hyp. done.
    - case (odd_or_even n) => [OddN|EvenN].
      + case NotZeroN => [Is3k|Not3k].
        have Isexp3k: exists k:nat,n=3.^k. by exists k. done.
      + case Not3k => [Short|Long].
        * move:(Short). move/andP. case=>[Short1 Short2].
        * apply (Three_Color_Triangle_Problem_nec_ShortOdd x n k).
          rewrite Short2. rewrite OddN. 
          apply /andP. rewrite Short1. done.
          move=> Cpos  H_uniq H_exists H_mix c c0 c1 Cpos0 Cpos1 [Cpos2a [Cpos2b Cpos2c]]. rewrite add0n in Cpos2c. 
          specialize (WCT Cpos). by apply WCT. 
        * by apply (Three_Color_Triangle_Problem_nec_LongOdd x n k). 
      + apply (Three_Color_Triangle_Problem_nec_even x n).
        rewrite NotZeroN_hyp. by rewrite EvenN. apply WCT.
  Qed.

  Proof.
    move=> n x NotZeroN_hyp; apply Contraposition; move=> Notexp3k.
    by apply Three_Color_Triangle_Problem_nec'.
  Qed.
   *)

  Theorem Three_Color_Triangle_Problem_sufnec :
    forall (n x : nat) , n > 0 -> (exists k : nat, n = 3 .^ k) <-> (WellColoredTriangleF x n). 
  Proof.
    move=> n x NotZeroN. split.
    - by apply Three_Color_Triangle_Problem_suf.
    - by apply Three_Color_Triangle_Problem_nec.
  Qed.
  
  (* 終わり *)
  Theorem Three_Color_Triangle_Problem2  :
    forall (n : nat) , n > 0 -> (exists k : nat, n = 3 .^ k) <-> (WellColoredTriangleF 0 n).
  Proof.
    move=>n. by apply Three_Color_Triangle_Problem_sufnec. 
  Qed.
  
(* ------------------------------------------------------------------------------ *)
  


(*  Cpos に関する定義．Ver6 では削除
  (*
  Variable Cpos :  nat -> nat -> Color -> Prop.
  (* 逆三角形の左から x:nat 番目，上から y:nat 番目の色が c:Color である *)
  *)

  Definition Triangle Cpos x y n c0 c1 c2 :=
    Cpos x y c0 /\ Cpos (x+n) y c1 /\ Cpos x (y+n) c2 -> c2 = mix c0 c1.

  Definition Cconf (c0 c1 c2 : Color) :=
    (c0 = c1 /\ c1 = c2 /\ c2 = c0) \/ (c0 <> c1 /\ c1 <> c2 /\ c2 <> c0).

  (* ----- 公理一覧 ----- *)
  Definition C_exists (Cpos:nat->nat->Color->Prop) := forall x y : nat, (exists c : Color, Cpos x y c).
  (* (C_exists Cpos): 塗り方 Cpos はすべてのマスに色が塗られている *)

  Definition C_uniq (Cpos:nat->nat->Color->Prop) := forall x y : nat, forall c0 c1 : Color, (Cpos x y c0 /\ Cpos x y c1) -> c0 = c1.
  (* (C_uniq Cpos) 1つのマスに塗れる色は1色までである *)

  Definition C_mix (Cpos:nat->nat->Color->Prop) := forall x y : nat, forall c0 c1 c2 : Color, (Cpos x y c0 /\ Cpos (x + 1) y c1 /\ Cpos x (y + 1) c2) -> c2 = mix c0 c1. 
  (* C_mix Cpos: 隣接する2つのマスの色に演算 mix を適用すると下のマスの色が決まる *)
  
  (* Axiom C_paint : forall x i : nat, forall f:nat -> Color, Cpos (x+i) 0 (f (x+i)). *)
  (* 最上行のどの場所も好きな色を塗ることができる *)

  (* 始点 (x,0) で一辺 n の三角形に，条件を満たすような任意の色塗りをしても三頂点は調和する *)
  Definition WellColoredTriangle x n := 
    (forall Cpos: nat->nat->Color->Prop, 
        C_uniq Cpos ->
        C_exists Cpos ->
        C_mix Cpos ->          
        forall (c c0 c1: Color),
          Cpos x 0 c0 ->
          Cpos (x+n) 0 c1 ->
          Cpos x n c -> 
          Triangle Cpos x 0 n c0 c1 c).
*)  
 
  
  (* ----- 三角形三色問題 ----- *)
(*  
  Lemma Three_Color_Triangle_Problem_suf' :
    forall Cpos: nat->nat->Color->Prop, forall (k n x y : nat) (c0 c1 c2 : Color),
        n = 3 .^ k
        -> C_mix Cpos
        -> C_exists Cpos
        -> Triangle Cpos x y n c0 c1 c2.
  Proof.
    move=>Cpos k n x y c0 c1 c2 H H_mix H_exists.
    move: k n x y c0 c1 c2 H. 
    elim=> [ | k IHk ].
    - move=> n x y c0 c1 c2 Step.
      rewrite expn0 in Step. rewrite Step.
      rewrite /Triangle. by apply H_mix.
    - move=> n x y c0 c1 c2 Step.
      move=> [] Cpos0. move=> [] Cpos1 Cpos2.
      
      (* マスに塗られている色に名前をつける *)
      + have: exists c : Color, Cpos (x+3.^k) y c.
        by apply H_exists. case; move=> c3 Cpos3.
      + have: exists c : Color, Cpos (x+((3.^k).*2)) y c.
        by apply (H_exists ((x+(3.^k).*2)) y). case; move=> c4 Cpos4.
      + have: exists c : Color, Cpos x (y+3.^ k) c.
        by apply (H_exists x (y+3.^k)). case; move=> c5 Cpos5.
      + have: exists c : Color, Cpos (x+3.^k) (y+3.^k) c.
        by apply (H_exists (x+3.^k) (y+3.^k)). case; move=> c6 Cpos6.
      + have: exists c : Color, Cpos (x+(3.^k).*2) (y+3.^k) c.
        by apply (H_exists (x+(3.^k).*2) (y+3.^k)). case; move=> c7 Cpos7.
      + have: exists c : Color, Cpos x (y+(3.^k).*2) c.
        by apply (H_exists x (y + (3.^k).*2)). case; move=> c8 Cpos8.
      + have: exists c : Color, Cpos (x+3.^k) (y + (3.^k).*2) c.
         by apply (H_exists (x+3.^k) (y + (3.^k).*2)). case; move=> c9 Cpos9.
          
      (* 6 個の 3 .^ k 段の逆三角形 *)
      + have Triangle035 : Triangle Cpos x y (3.^k) c0 c3 c5.
        by apply IHk.
      + have Triangle346 : Triangle Cpos (x+3.^k) y (3.^k) c3 c4 c6.
        by apply IHk.
      + have Triangle417 : Triangle Cpos (x+(3.^k).*2) y (3.^k) c4 c1 c7.
        by apply IHk.
      + have Triangle568 : Triangle Cpos x (y+3.^k) (3.^k) c5 c6 c8.
        by apply IHk.
      + have Triangle679 : Triangle Cpos (x+3.^k) (y+3.^k) (3.^k) c6 c7 c9.
        by apply IHk.
      + have Triangle892 : Triangle Cpos x (y+(3.^k).*2) (3.^k) c8 c9 c2.
        by apply IHk.
        
    (* それぞれの逆三角形における Cpos の関係から mix の関係を導く *)
      + have mix035 : c5 = mix c0 c3.
        apply Triangle035. done.
      + have mix346 : c6 = mix c3 c4.
        apply Triangle346.
        * split. done.
        * split. rewrite- addnA; rewrite add3n3n mul2n. done.
        * done.
      + have mix417 : c7 = mix c4 c1.
        apply Triangle417.
        * split. done.
        * split. rewrite- mul2n.
           rewrite- addnA. rewrite add23n3n. rewrite- Step. done.
        * done.
      + have mix568 : c8 = mix c5 c6.
        apply Triangle568.
        * split. done.
        * split. done.
        * rewrite- addnA; rewrite add3n3n mul2n. done.
      + have mix679 : c9 = mix c6 c7.
        apply Triangle679.
        * split. done.
        * split. rewrite- addnA; rewrite add3n3n mul2n. done.
        * rewrite- addnA; rewrite add3n3n mul2n. done.
      + have mix892 : c2 = mix c8 c9.
        apply Triangle892.
        * split. done.
        * split. done.
        * rewrite- addnA. rewrite- mul2n. rewrite add23n3n. rewrite- Step.
          done.

      (* mixCut を用いて証明を完了させる *)
      rewrite mix568 mix679 in mix892.
      rewrite mix035 mix346 mix417 in mix892.
      rewrite mix892. by apply mixCut.
  Qed.

  Theorem Three_Color_Triangle_Problem_suf'' :
    forall (x y n : nat),
      (exists k : nat, n = 3 .^ k) ->
      forall Cpos:nat->nat->Color->Prop, forall (c0 c1 c2 : Color),
        C_mix Cpos
        -> C_exists Cpos
        -> Triangle Cpos x y n c0 c1 c2.
  Proof.
    move=> x y n Step Cpos H_mix H_exists.
    move:Step. case; move=> k Step c0 c1 c2.
    by apply (Three_Color_Triangle_Problem_suf' Cpos k n x y).
  Qed.

  Theorem Three_Color_Triangle_Problem_suf :
    forall (x n : nat),
      (exists k : nat, n = 3 .^ k) -> (WellColoredTriangle x n). 
  Proof.
    rewrite /WellColoredTriangle.
    move=> x n Step Cpos H_uniq H_exists H_mix c c0 c1 Cpos0 Cposxn Cposyn.
    by apply Three_Color_Triangle_Problem_suf''.    
  Qed.











  
  Fixpoint F (f : nat -> Color) (x y : nat) : Color :=
    match y with
    | 0 => f x
    | y'.+1 => mix (F f x y') (F f(x.+1) y')
    end.

  Definition CposF f x y c : Prop := (c = F f x y).

  (* Definition TriangleF f x y n c0 c1 c2 := *)
  (*   (CposF f x y c0 /\ CposF f (x+n) y c1 /\ CposF f x (y+n) c2) -> c2 = mix c0 c1. *)

  Lemma C_exists_F :
    forall(f:nat->Color) (x y:nat), exists(c:Color), CposF f x y c.
  Proof.
    move=> f x. case.
    - exists (f x). done.
    - move=> y'. exists (mix (F f x y') (F f(x.+1) y')). done.
  Qed.

  Lemma C_uniq_F :
    forall(f:nat->Color) (x y:nat) (c0 c1:Color),      
      (CposF f x y c0 /\ CposF f x y c1) -> c0 = c1.
  Proof.
    move=> f x y c0 c1 [] CposF0 CposF1.
    rewrite /CposF in CposF0 CposF1.
    rewrite CposF0 CposF1. done.
  Qed.

  Lemma C_mix_F :
    forall(f:nat->Color) (x y:nat) (c0 c1 c2:Color),
      (CposF f x y c0 /\ CposF f (x.+1) y c1 /\ CposF f x (y.+1) c2) -> c2 = mix c0 c1.
  Proof.
    move=> f x y c0 c1 c2 [] CposF0; move=> [] CposF1 CposF2.
    rewrite /CposF in CposF0 CposF1 CposF2.
    rewrite CposF0 CposF1 CposF2.
    rewrite /F. rewrite- /F. done.
  Qed.

  Lemma C_paint' :
    forall (f : nat -> Color), exists(Cpos' : nat -> nat -> Color -> Prop),
        C_uniq Cpos' /\ C_exists Cpos' /\ C_mix Cpos'
        /\ forall (x i : nat), Cpos' (x+i) 0 (f (x+i)).
  Proof.
    move=> f.
    exists (CposF f). 
    split. rewrite /C_uniq. apply (C_uniq_F f).
    split. rewrite /C_exists. apply (C_exists_F f).
    split. rewrite /C_mix. move=> x y c0 c1 c2.
    do ! rewrite addn1. apply (C_mix_F f). by rewrite /CposF /F.
  Qed.
*)

  
  Lemma rangeN3 : forall n : nat, exists k : nat, (n = 0) \/ (3.^k <= n <= (3.^k).*2) \/ ((3.^k).*2 + 1 <= n < (3.^(k.+1))).
  Proof.
    elim=> [ | n IHn].
    - exists 0. left. done.
    - move: IHn. case. move=> k IHn.
      case IHn.
      + move=> Zero.
        rewrite Zero. exists 0. rewrite /=. right; left. done.
      (* n.+1 = 1 と n.+1 > 1 で場合分け *)
      + case (case1 n) => [Zero|NotZero].      
        (* n.+1 = 1 のとき *)
        * rewrite Zero. exists 0. right; left. by rewrite /=.
        (* n.+1 > 1 のとき *)
        * rewrite Short1 Long1 connect3m. move /andP. move => rangeN.         
          (* n.+1 = 3 .^ k と n.+1 < 3 .^ k.+1で場合分け *)
          have rangeBoundary : (n.+1 = 3 .^ k.+1) \/ (n.+1 < 3 .^ k.+1).
          move: rangeN. move /andP; move=> [] ranegeN1 rangeN2.
          rewrite Boundary. apply /orP. by rewrite leq_eqVlt in rangeN2.
          case rangeBoundary => [rangeN1|rangeN2].
          (* n.+1 = 3 .^ k のとき *)
          ** exists (k.+1). rewrite rangeN1. right; left.
             apply /andP. split. done.
             rewrite- addnn. rewrite- {1} (add0n (3.^k.+1)). rewrite- eq_mono_plus_le_plus. done. 
          ** exists k. rewrite Short2 Long2 connect3m. right. split.
             move: rangeN. move /andP. move=> [] range1 range2.
             apply leqW. done. done.
  Qed.        

  Lemma rangeN4 : forall n : nat, exists k : nat, (n = 0) \/ (n = 3.^k) \/ (3.^k < n <= (3.^k).*2) \/ ((3.^k).*2 + 1 <= n < (3.^(k.+1))).
  Proof.
    move=> n.
    have [k H]: exists k:nat, (n = 0) \/ (3.^k <= n <= (3.^k).*2) \/ ((3.^k).*2 + 1 <= n < (3.^(k.+1))).
    apply rangeN3. exists k.
    suff K: ((n = 3 .^ k) \/ (3 .^ k < n <= (3.^k).*2)) <-> (3.^k <= n <= (3.^k).*2).
    + destruct H. by left. 
      destruct H. right. apply/or_assoc. left. by apply/K.
      right. right. right. done.       (* proof end *)
      (* proof of K *) split.
    + (* -> of K *)
      case. move=>L. rewrite- L. rewrite leqnn. rewrite self_double. done.
      move/andP. move=>[L1 L2]. rewrite L2. rewrite Bool.andb_true_r. by apply ltnW. 
    + (* <- of K *)
      move/andP. move=>[L1 L2]. rewrite L2. rewrite Bool.andb_true_r. 
      rewrite leq_eqVlt in L1. apply Bool.orb_true_iff in L1.
      destruct L1. move/eqP in H0. rewrite H0. by left. move/ltP in H0. right. by apply/coqnat_lt. 
  Qed.

  (* ある段が全て赤ならその下はずっと赤 (Red_N と似ているが，x の範囲制限つき) *)  
  Lemma AllRedN :
    forall Cpos:nat->nat->Color->Prop, forall x y n : nat,
        C_exists Cpos
        -> C_mix Cpos        
        -> (forall i :nat, (0 <= i <= n -> Cpos (x+i) y red))
        -> forall q p : nat, (0 <= p+q <= n ->  Cpos (x+p) (y+q) red).
  Proof.
    move=> Cpos x y n H_exists H_mix topcolor.
    induction q.
    - (* base case: q is 0 *)
      move=> p. 
      rewrite ! addn0. apply topcolor. 
    - (* induction case: q is successor *)
      move=> p. move/andP. move =>[rangePQ1 rangePQ2].
      + have prevL: Cpos (x+p) (y+q) red.
        apply IHq.
        apply /andP. split. done.
        rewrite addnS in rangePQ2. by apply ltnW. 
      + have prevR: Cpos ((x+p).+1) (y+q) red.
        rewrite- (addnS x p). 
        apply IHq. apply /andP. split. done. 
        rewrite addSn. rewrite addnS in rangePQ2. done.
    - have [c Red'] : exists c : Color, Cpos (x+p) (y+q+1) c.
        by apply H_exists.
    - have Mix : c = mix red red.
      rewrite- addn1 in prevR. 
      rewrite- addn1 in Red'. apply (H_mix (x+p) (y+q)). by split. 
    - rewrite /= in Mix. rewrite- Mix. rewrite addnS. rewrite- addn1. done. 
  Qed.

  (* ある段が全て赤なら最下段も赤 *)
  Lemma AllRed:
    forall Cpos:nat->nat->Color->Prop, forall x y n : nat,
        C_exists Cpos
        -> C_mix Cpos
        -> (forall i :nat, (0 <= i <= n -> Cpos (x+i) y red))
        -> Cpos x (y+n) red.
  Proof.
    move=> Cpos x y n H_exists H_mix topcolor.
    have fromAllRedN: forall q p : nat, (0 <= p+q <= n ->  Cpos (x+p) (y+q) red).
    apply AllRedN. done. done. done.
    generalize (fromAllRedN n 0). rewrite addn0. rewrite add0n.
    move=> A. apply A. apply/andP. done. 
  Qed.

  (* Three_Color_Triangle_Problem_nec_even のための定義と補題群 *)
  (* colorYB x n z : 最上段の x から x+n までのマスを黄，青と交互に塗る (範囲外は黄にする) *)
  Definition colorYB (x n z : nat) :=
    if (0 <= z-x <= n) && (odd (z-x) == false) then yel
    else if (0 <= z-x <= n) && (odd (z-x) == true) then blu
         else blu.
  
  (* colorYB の性質1 *)
  Lemma lemYB1: forall x n i : nat, (0 <= i <= n) && (odd i == false) -> colorYB x n (x + i) = yel.
  Proof.
    move=> x n i range.
    rewrite- (x_plus_y_minus_x_is_y x i) in range.
    rewrite /colorYB.
    rewrite range. by rewrite /=.
  Qed.

  (* colorYB の性質2 *)
  Lemma lemYB2: forall x n i: nat, (0 <= i <= n) && (odd i == true) -> colorYB x n (x+i) = blu.
  Proof.
    move=> x n i.
    move /andP. move=> [] range.
    move /eqP. move=> [] oddI.
    rewrite- (x_plus_y_minus_x_is_y x i) in range.
    rewrite- (x_plus_y_minus_x_is_y x i) in oddI.
    rewrite /colorYB. rewrite range oddI. by rewrite /=.
  Qed.
  
  (* colorYB の性質3 *)
  Lemma lemYB3: forall x n i: nat, (odd n == false) -> colorYB x n x = colorYB x n (x+n).
  Proof.
    move=> x n i. move /eqP => oddN.
    rewrite /colorYB. rewrite subnn.
    - have range0 : (0 <= 0 <= n) && (ssrnat.odd 0 == false).
      rewrite /=. done.
      rewrite range0.
    - rewrite (x_plus_y_minus_x_is_y x n).
      have rangeN : (0 <= n <= n) && (ssrnat.odd n == false).
      rewrite oddN. rewrite leqnn. rewrite /=. done.
      rewrite rangeN. done.
  Qed.

  Lemma EvenA :
    forall Cpos:nat->nat->Color->Prop, forall x n : nat,
        n > 0
        -> C_exists Cpos
        -> C_mix Cpos
        -> (forall i : nat, ((0 <= i <= n) -> Cpos (x+i) 0 (colorYB x n (x+i))))
        -> forall i : nat, ((0 <= i <= n.-1) -> Cpos (x+i) 1 red).
  Proof.
    move=> Cpos x n NotZero H_exists H_mix topcolor i range.
    
    (* 最上段のマスが colorYB で塗られていることを示す *)
    - have rangetop1 : 0 <= i <= n.
      apply /andP. split. done.
      move: range. move /andP. move=> [] rangetop1a rangetop1b.
      apply (trans_lelele rangetop1b). apply leq_pred.
      generalize (topcolor i) => Cpos1. specialize (Cpos1 rangetop1).
    - have rangetop2 : 0 <= i.+1 <= n.
      apply /andP. split. done.
      move: range. move /andP. move=> [] rangetop2a rangetop2b.
      have S_pred : (i.+1 <= n) = (i <= n.-1).
      apply eq_adjoint_S_P_le. done.
      rewrite S_pred. done. rewrite- addn1 in rangetop2.
      generalize (topcolor (i+1)) => Cpos2. specialize (Cpos2 rangetop2).

    (* 最上段より 1 段下のマスの色は mix と colorYB で得られることを示す *)
    - have Cpos3 : exists c : Color, Cpos (x+i) 1 c.
      apply H_exists. move: Cpos3. case. move=> c Cpos3.
      have Color : c = mix (colorYB x n (x + i)) (colorYB x n (x + (i + 1))).
      apply (H_mix (x+i) 0).
      split. done. split. rewrite- addnA. done. done.
      rewrite Color in Cpos3.

    (* colorYB で塗られている色を示す *)
    - case (odd_or_even i) => [OddI|EvenI].
      
    (* i が奇数のとき *)
      + have Color1 : colorYB x n (x + i) = blu.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangetop1 OddI. done.
      + have Color2 : colorYB x n (x + (i + 1)) = yel.
        have OddI1 : odd (i+1) = false.
        rewrite addn1 oddS. by rewrite OddI.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangetop2 OddI1. done.
      + rewrite Color1 Color2 in Cpos3. by rewrite /= in Cpos3.
        
    (* i が偶数のとき *)
      + have Color1 : colorYB x n (x + i) = yel.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangetop1 EvenI. done.
      + have Color2 : colorYB x n (x + (i + 1)) = blu.
        have OddI1 : odd (i+1) = true.
        rewrite addn1 oddS. by rewrite EvenI.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangetop2 OddI1. done.
      + rewrite Color1 Color2 in Cpos3. by rewrite /= in Cpos3.
  Qed.
  
  Lemma EvenB :
    forall Cpos:nat->nat->Color->Prop, forall x n : nat,
        n > 0
        -> C_exists Cpos
        -> C_mix Cpos
        -> (forall i : nat, ((0 <= i <= n) -> Cpos (x+i) 0 (colorYB x n (x+i))))
        -> Cpos x n red.
  Proof.
    move=> Cpos x n NotZero H_exists H_mix topcolor.
    have AllRed1 : forall i : nat, (0 <= i <= n.-1) -> Cpos (x+i) 1 red.
    apply EvenA. done. done. done. done. 
    have YN : 0 + n = (0 + 1) + (n - 1).
    rewrite addnAC. rewrite- addnA. rewrite subn1 addn1.
    rewrite add0n add0n. 
    have pred_S : n.-1.+1 = n.
    apply prednK. done. rewrite pred_S. done. 
    rewrite-[n] add0n. rewrite YN.
    apply AllRed. done. done. by rewrite subn1.
  Qed.

  Lemma Three_Color_Triangle_Problem_nec_even :
    forall x n :nat,
      (n > 0) && (odd n == false) ->
      ~(forall Cpos: nat->nat->Color->Prop, 
               C_uniq Cpos ->
               C_exists Cpos ->
               C_mix Cpos ->
               forall (c c0 c1: Color),
                 Cpos x 0 c0 ->
                 Cpos (x+n) 0 c1 ->
                 Cpos x n c ->                 
                 Triangle Cpos x 0 n c0 c1 c).
  Proof.
    move=> x n.
    move /andP; move=> [] NotZeroN OddN Triangle_hyp.
    have H_CposYB: exists Cpos' : nat -> nat -> Color -> Prop,C_uniq Cpos' /\ C_exists Cpos' /\ C_mix Cpos' /\ (forall x0 i : nat, Cpos' (x0 + i) 0 (colorYB x n (x0 + i))). 
    apply (C_paint' (colorYB x n)).
    move:H_CposYB.  case=> CposYB [H_uniq [H_exists [H_mix H]]].
    specialize (Triangle_hyp CposYB H_uniq H_exists H_mix).
    have topcolor : forall i : nat, ((0 <= i <= n) -> CposYB (x+i) 0 (colorYB x n (x+i))).
    move=>i range. apply H. 
    
    (* 最下段のマスの色が異なることで矛盾を導く *)
    
    (* EvenB より最下段のマスの色が red であることを示す．*)
    - have CposR : CposYB x n red. by apply EvenB.

    (* Triangle_hyp 等を用いて最下段のマスの色が yel であることを示す *)
    (* 最上段の両端のマスを colorYB を用いて塗ることを示す *) 
    - have : (0 <= 0 <= n) && (odd 0 == false).
      rewrite /=. done.
      move /andP; move=> [] range0a range0b.
      generalize (topcolor 0) => Cpos0. specialize (Cpos0 range0a).
    - have : (0 <= n <= n) && (odd n == false).
      rewrite OddN. rewrite leqnn. rewrite /=. done.
      move /andP; move=> [] rangeNa rangeNb.
      generalize (topcolor n) => CposN. specialize (CposN rangeNa).

    (* 最下段の色が Triangle_hyp より mix で得られることを示す *)
    - have : exists c : Color, CposYB x n c. apply H_exists.
      case. move=> c CposY.
      generalize (Triangle_hyp c (colorYB x n x)) => TriangleN.
      have ColorBelow : c = mix (colorYB x n x) (colorYB x n (x + n)).
      apply TriangleN. rewrite addn0 in Cpos0. done. done. done. split.
      rewrite eq_unit_plus_l in Cpos0. done. done. 
      
    (* CposY の色が yel であることを示す *)
    - have sameColor : colorYB x n x = colorYB x n (x + n).
      apply lemYB3; done. rewrite- sameColor in ColorBelow.
      have ColorY : colorYB x n x = yel.
      rewrite /colorYB. rewrite x_minus_x_is_0. by rewrite range0a.
      rewrite ColorY in ColorBelow. rewrite /= in ColorBelow.
      rewrite ColorBelow in CposY.

    (* falseColor より矛盾を示す *)
    - apply (falseColor CposYB x n red yel). apply H_uniq. 
      split. done. split. done. done.  
  Qed.

  (* Three_Color_Triangle_Problem_nec_oddA のための定義と補題群 *)
  (* colorYB x n k z : 最上段の x から x+n までのマスを黄，青と交互に塗る (範囲外は黄にする) *)
  Definition colorYBBY (x n z : nat) :=
    if (0 <= z-x <= n./2) && (odd (z-x) == false) then yel
    else if (n./2.+1 <= z-x <= n) && (odd (z-x) == true) then yel
         else if (0 <= z-x <= n./2) && (odd (z-x) == true) then blu
              else if (n./2.+1 <= z-x <= n) && (odd (z-x) == false) then blu
                   else yel.
  
  (* colorYBBY の性質1 *)
  Lemma lemYBBY1:
    forall x n i : nat, (0 <= i <= n./2) && (odd i == false) -> colorYBBY x n (x + i) = yel.
  Proof.
    move=> x n i.
    move /andP. move=> [] range.
    move /eqP. move=> [] oddI.
    rewrite- (x_plus_y_minus_x_is_y x i) in range.
    rewrite- (x_plus_y_minus_x_is_y x i) in oddI.
    rewrite /colorYBBY. rewrite range oddI. by rewrite /=.
  Qed.

  (* colorYB の性質2 *)
  Lemma lemYBBY2: forall x n i: nat, (n./2.+1 <= i <= n) && (odd i == true) -> colorYBBY x n (x+i) = yel.
  Proof.
    move=> x n i.
    move /andP. move=> [] range.
    move /eqP. move=> [] oddI.
    rewrite- (x_plus_y_minus_x_is_y x i) in range.
    rewrite- (x_plus_y_minus_x_is_y x i) in oddI.
    rewrite /colorYBBY. rewrite range oddI.
    have range_false : n./2 < x + i - x <= n -> (0 <= x + i - x <= n./2) = false.
    apply leq_false1. specialize (range_false range).
    rewrite range_false. by rewrite /=.    
  Qed.

  (* colorYBBY の性質3 *)
  Lemma lemYBBY3: forall x n i: nat, (0 <= i <= n./2) && (odd i == true) -> colorYBBY x n (x+i) = blu.
  Proof.
    move=> x n i.
    move /andP. move=> [] range.
    move /eqP. move=> [] oddI.
    rewrite- (x_plus_y_minus_x_is_y x i) in range.
    rewrite- (x_plus_y_minus_x_is_y x i) in oddI.
    rewrite /colorYBBY. rewrite range oddI.
    have range_false : 0 <= x + i - x <= n./2 -> (n./2.+1 <= x + i - x <= n) = false.
    apply leq_false2. specialize (range_false range).
    rewrite range_false. by rewrite /=.
  Qed.
  
  (* colorYBBY の性質4 *)
  Lemma lemYBBY4: forall x n i: nat, (n./2.+1 <= i <= n) && (odd i == false) -> colorYBBY x n (x+i) = blu.
  Proof.
    move=> x n i.
    move /andP. move=> [] range.
    move /eqP. move=> [] oddI.
    rewrite- (x_plus_y_minus_x_is_y x i) in range.
    rewrite- (x_plus_y_minus_x_is_y x i) in oddI.
    rewrite /colorYBBY. rewrite range oddI.
    have range_false : n./2 < x + i - x <= n -> (0 <= x + i - x <= n./2) = false.
    apply leq_false1. specialize (range_false range).
    rewrite range_false. by rewrite /=.
  Qed.
  
  (* colorYBBY の性質5 *)
  Lemma lemYBBY5: forall x n : nat, (odd n == true) -> colorYBBY x n x = colorYBBY x n (x+n).
  Proof.
    move=> x n.  move /eqP => oddN.
    rewrite /colorYBBY. rewrite subnn.
    - have range0 : (0 <= 0 <= n./2) && (ssrnat.odd 0 == false).
      rewrite /=. done.
      rewrite range0.
    - rewrite (x_plus_y_minus_x_is_y x n). rewrite oddN.
      have rangeN1 : ((0 <= n <= n./2) && (true == false)) = false.
      rewrite andbF. done. rewrite rangeN1.
    - have rangeN2 : n./2.+1 <= n <= n.
      apply /andP. split. rewrite eq_adjoint_half_double_lt. rewrite- addnn. 
      rewrite- eq_S_le_add_r. by apply odd_gt0. done. 
      rewrite rangeN2. by rewrite /=.
  Qed.

  Lemma ShortOddA :
    forall Cpos:nat->nat->Color->Prop,forall x n k : nat,
        ((3.^k < n <= (3.^k).*2) && (odd n == true))
        -> C_exists Cpos
        -> C_mix Cpos
        -> C_uniq Cpos              
        -> (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle Cpos x1 y1 (3 .^ k) c0 c1 c2)
        -> (forall i : nat, ((0 <= i <= n) -> Cpos (x+i) 0 (colorYBBY x n (x+i))))
        -> (forall i : nat, ((0 <= i <= n - 3.^k) -> Cpos (x+i) (3.^k) (colorYB x (n-3.^k) (x+i)))).
  Proof.
    move=> Cpos x n k H H_exists H_mix H_uniq. move:H. 
    move/andP. case=>[A B]. move:(A). move/andP. case=>[A1 A2]. move=>triangle color i rangeI.
    move: (rangeI). move/andP. case=>[rangeI1 rangeI2].
    - have A3: n < (3.^k).*2. rewrite eq_le_eq_lt in A2. move:A2. move/orP. case. move=>P.
      have B': odd ((3.^k).*2). move/eqP in P. rewrite- P. move/eqP in B. done. rewrite odd_double in B'. done. done.
    - have B': odd n = true. by apply/eqP.
    - have E: 3 .^ k <= n. by apply ltnW.       
    - have C1: 1+(n./2).*2 = n. rewrite- {2} (odd_double_half n). rewrite B'. done.
    - have C2: (n./2).*2 = n.-1. apply/eqP. rewrite- eq_adjoint_S_P_eq. apply/eqP. done. by apply odd_gt0.
    - have C3: n-(n./2) = (n./2).+1. apply/eqP. rewrite eq_adjoint_minus_plus_eq. apply/eqP.     
      rewrite- addn1. rewrite eq_comm_plus. rewrite- eq_assoc_plus. rewrite addnn. by rewrite eq_comm_plus.
      apply self_half. 
    - have C4: n./2 < 3.^k. by rewrite eq_adjoint_half_double_lt.
    - have C5: n-3.^k <= n./2. rewrite eq_adjoint_minus_plus_le. rewrite eq_comm_plus.
      rewrite- eq_adjoint_minus_plus_le. rewrite C3. done. 
    - have C6: i<=n./2. apply (trans_lelele rangeI2). done.
    - have C7: n./2 < i + 3 .^ k. apply (trans_ltlelt C4). rewrite eq_comm_plus. apply leq_addr.
    - have C8: i + 3 .^ k <= n. rewrite eq_adjoint_plus_minus_le. done. done. 
    - have C9: odd (3.^k). by apply odd3m.
    - have rangeIa: 0 <= i <= n.
      apply/andP; split. done. apply (trans_lelele rangeI2); apply leq_subr.
    - have rangeIb: 0 <= (i+3.^k) <= n.
      apply/andP; split. apply (trans_lelele rangeI1); apply leq_addr. rewrite eq_adjoint_plus_minus_le. done. done.
    - have posN: 0<n. by apply odd_gt0.
    - have Cpos1: Cpos (x+i) 0 (colorYBBY x n (x+i)).
      apply color. apply rangeIa.
    - have Cpos2: Cpos (x+i+3.^k) 0 (colorYBBY x n (x+i+3.^k)).
      rewrite eq_assoc_plus. apply color. apply rangeIb.      
    - have [c' Cpos3]: exists c:Color, Cpos (x+i) (3.^k) c. by apply H_exists.
    - have mix: c' = mix (colorYBBY x n (x+i)) (colorYBBY x n (x+i+3.^k)).
      by apply (triangle (x+i) 0 (colorYBBY x n (x+i)) (colorYBBY x n (x+i+3.^k))).
    - have or: odd i || ~~odd i. apply orbN. move/orP in or. case:or=> [oddI|evenI].
      + (* Case of oddI *)
        have blu1: colorYBBY x n (x+i) = blu.
        apply lemYBBY3. apply/andP. split. apply/andP; split. done. by apply (trans_lelele rangeI2). by rewrite oddI.
        have blu2: colorYBBY x n (x+i+3.^k) = blu.
        rewrite (eq_assoc_plus x i (3.^k)). apply lemYBBY4.
        apply/andP. split. apply/andP; split. rewrite- eq_adjoint_half_double_lt in A3. 
        apply (trans_ltltlt A3). rewrite- {1} (add0n (3.^k)). rewrite- eq_mono_plus_lt_plus. by apply odd_gt0. done.
        rewrite eq_odd_plus. by rewrite C9. done.
        have c'_is_blu: c' = blu. rewrite blu1 in mix. rewrite blu2 in mix. by simpl in mix.
        have c'_of_colorYB: colorYB x (n-3.^k) (x+i) = c'.
        rewrite c'_is_blu. apply lemYB2. rewrite oddI. by rewrite rangeI. by rewrite c'_of_colorYB.
      + (* Case of evenI *)
        have yel1: colorYBBY x n (x+i) = yel.
        apply lemYBBY1. rewrite- eq_false in evenI. rewrite evenI. rewrite rangeI1. rewrite C6. done.
        have yel2: colorYBBY x n (x+i+3.^k) = yel. rewrite eq_assoc_plus. 
        apply lemYBBY2. rewrite C7. rewrite C8. simpl. rewrite eq_even_plus. by rewrite C9. done. 
        have c'_is_yel: c' = yel. rewrite yel1 in mix. rewrite yel2 in mix. by simpl in mix.
        have c'_of_colorYB: colorYB x (n-3.^k) (x+i) = c'.
        rewrite c'_is_yel. apply lemYB1. rewrite rangeI. rewrite- eq_false in evenI. done.
        by rewrite c'_of_colorYB.
  Qed.
  
  Lemma ShortOddB :
    forall Cpos:nat->nat->Color->Prop,forall x n k : nat,
        ((3.^k < n <= (3.^k).*2) && (odd n == true))
        -> C_exists Cpos
        -> C_mix Cpos
        -> C_uniq Cpos              
        -> (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle Cpos x1 y1 (3 .^ k) c0 c1 c2) 
        -> (forall i : nat, ((0 <= i <= n) -> Cpos (x+i) 0 (colorYBBY x n (x+i))))
        -> (forall i : nat, ((0 <= i <= (n - 3.^k).-1) -> Cpos (x+i) ((3.^k).+1) red)).
  Proof.
    move=> Cpos x n k cond1 H_exists H_mix H_uniq triangle color i rangeI.
    move: (rangeI). move/andP. case=>[C1 C2].
    move: cond1. move/andP. case=>[rangeN oddN]. move:(oddN). move/eqP =>oddN'.
    move:(rangeN). move/andP. case=>[rangeN1 rangeN2].
    have C3: n>0. have D: 0<=3.^k. apply leq0n. apply (trans_leltlt D). done.
    have C4 : 0 < n - 3 .^ k.
    rewrite ltn_subCr. rewrite subn0. done.
    have fromOddA: forall i:nat, (0<=i<=n-3.^k -> Cpos (x+i) (3.^k) (colorYB x (n-3.^k) (x+i))).
    apply ShortOddA. apply /andP. rewrite oddN'. by rewrite rangeN. done. done. done. done. done. 
    have rangeI1 : 0 <= i <= n - 3 .^ k.
    apply /andP. split. done.
    apply (leq_trans C2). apply leq_pred.
    have rangeI2 : 0 <= i.+1 <= n - 3 .^ k.
    apply /andP. split. done.
    apply (leq_ltn_trans C2).
    rewrite ltn_predL. done.

    (* 3^k 段下のマスの色は colorYB で塗られていることを示す *)
    have Cpos1 : Cpos (x + i) (3 .^ k) (colorYB x (n - 3.^k) (x + i)).
    generalize (fromOddA i) => Cpos1.
    specialize (Cpos1 rangeI1). done.
    have Cpos2 : Cpos (x + i).+1 (3 .^ k) (colorYB x (n - 3.^k) (x + i).+1).
    generalize (fromOddA i.+1) => Cpos2.
    specialize (Cpos2 rangeI2).
    rewrite- addnS. done.
    rewrite- addn1 in Cpos2.
    
    (* 3^k + 1 段下のマスの色は mix と colorYB で得られることを示す *)
    have Cpos3 : exists c : Color, Cpos (x+i) (3.^k+1) c.
    apply H_exists. move: Cpos3. case. move=> c Cpos3.
    have Color : c = mix (colorYB x (n - 3 .^ k) (x + i)) (colorYB x (n - 3 .^ k) (x + i + 1)).
    apply (H_mix (x+i) (3.^k)).
    split. done. split. done. done.
    rewrite Color in Cpos3.

    (* colorYB で塗られている色を示す *)
    - case (odd_or_even i) => [OddI1|EvenI1].
      
    (* i が奇数のとき *)
      + have Color1 : colorYB x (n - 3 .^ k) (x + i) = blu.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangeI1 OddI1. done.
      + have Color2 : colorYB x (n - 3 .^ k) (x + i + 1) = yel.
        have OddI2 : odd i.+1 = false.
        rewrite oddS. by rewrite OddI1.
        rewrite /colorYB.  rewrite- addnA.
        rewrite x_plus_y_minus_x_is_y addn1.
        rewrite rangeI2 OddI2. done.
      + rewrite Color1 Color2 in Cpos3.
        rewrite /= in Cpos3. by rewrite- addn1.
        
    (* i が偶数のとき *)
      + have Color1 : colorYB x (n - 3 .^ k) (x + i) = yel.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangeI1 EvenI1. done.
      + have Color2 :colorYB x (n - 3 .^ k) (x + i + 1) = blu.
        have OddI2 : odd i.+1 = true.
        rewrite oddS. by rewrite EvenI1.
        rewrite /colorYB. rewrite- addnA.
        rewrite x_plus_y_minus_x_is_y addn1.
        rewrite rangeI2 OddI2. done.
      + rewrite Color1 Color2 in Cpos3.
        rewrite /= in Cpos3. by rewrite- addn1.
  Qed.
  
  Lemma ShortOddC :
    forall Cpos:nat->nat->Color->Prop,forall x n k : nat,
        ((3.^k < n <= (3.^k).*2) && (odd n == true))
        -> C_exists Cpos
        -> C_mix Cpos
        -> C_uniq Cpos              
        -> (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle Cpos x1 y1 (3 .^ k) c0 c1 c2) 
        -> (forall i : nat, ((0 <= i <= n) -> Cpos (x+i) 0 (colorYBBY x n (x+i)))) 
        -> Cpos x n red.
  Proof.
    move=> Cpos x n k cond H_exists H_mix H_uniq triangle color.
    move: (cond). move/andP. case=>[C1 C2].
    move: C1. move/andP. case=>[rangeN1 rangeN2]. 
    have fromOddB: forall i:nat, 0<=i<=(n-3.^k).-1 -> Cpos (x+i) ((3.^k).+1) red.
    apply ShortOddB. done. done. done. done. done. done. 
    have fromAllRed: Cpos x (((3.^k)+1)+((n-3.^k)-1)) red. 
    apply AllRed. done. done. rewrite subn1. rewrite addn1. done.
    have D: 0+n = (0 + 3 .^ k + 1 + (n - 3 .^ k - 1)).
    apply/eqP. rewrite eq_assoc_plus. rewrite eq_assoc_plus. 
    rewrite- eq_mono_plus_eq_plus_l. rewrite eq_comm_plus. 
    rewrite- eq_adjoint_minus_plus_eq. rewrite eq_comm_plus. 
    rewrite- eq_adjoint_minus_plus_eq. done.
    rewrite- eq_adjoint_plus_minus_lt. rewrite add0n. done.
    apply ltnW. done. 
    rewrite- D in fromAllRed. done. 
  Qed.
  
  Lemma Three_Color_Triangle_Problem_nec_ShortOdd :
    forall x n k : nat,
      ((3.^k < n <= (3.^k).*2) && (odd n == true))
      ->
      ~(forall Cpos: nat->nat->Color->Prop, 
           C_uniq Cpos ->
           C_exists Cpos ->
           C_mix Cpos ->
           forall (c c0 c1: Color),
             Cpos x 0 c0 ->
             Cpos (x+n) 0 c1 ->
             Triangle Cpos x 0 n c0 c1 c).
  Proof.
    - move=> x n k cond triangle.
      have H_CposYBBY: exists Cpos' : nat -> nat -> Color -> Prop,C_uniq Cpos' /\ C_exists Cpos' /\ C_mix Cpos' /\ (forall x0 i : nat, Cpos' (x0 + i) 0 (colorYBBY x n (x0 + i))). apply (C_paint' (colorYBBY x n)).
      move:H_CposYBBY; case=> [CposYBBY [H_uniq [H_exists [H_mix H]]]].
      specialize (triangle CposYBBY H_uniq H_exists).
      have topcolor : forall i : nat, ((0 <= i <= n) -> CposYBBY (x+i) 0 (colorYBBY x n (x+i))).
      move=>i range. apply H.       
      + move: (cond). move/andP. case=>[K1 K2].
      + have tri3k: forall x y: nat, forall c0 c1 c2: Color, Triangle CposYBBY x y (3.^k) c0 c1 c2.
        move=> x1 y1 c0 c1 c2. apply Three_Color_Triangle_Problem_suf''.
        exists k. done. done. done. 
      + have fromCpaint: forall i:nat,0<=i<=n -> CposYBBY (x+i) 0 (colorYBBY x n (x+i)).
        move=> i rangeI. done.
        
      + have fromOddC: CposYBBY x (0+n) red.
        apply (ShortOddC CposYBBY x n k). done. done. done. done. done. done. 
      + have A1: CposYBBY (x+0) 0 (colorYBBY x n (x+0)). apply fromCpaint. done. 
      + have A2: CposYBBY (x+n) 0 (colorYBBY x n (x+n)). apply fromCpaint.
        have B1: 0<=n. apply leq0n. have B2: n<=n. apply leqnn. rewrite B1. rewrite B2. done.
      + have [c' A3]: exists c':Color, CposYBBY x (0+n) c'. apply H_exists. 
      + have A4: Triangle CposYBBY x 0 n (colorYBBY x n x) (colorYBBY x n (x+n)) c'. apply triangle. done. rewrite addn0 in A1. done. done.
      + have mix1: c' = mix (colorYBBY x n x) (colorYBBY x n (x+n)). apply A4.
        split. rewrite- {1 3} (addn0 x). done. split. done. done. 
      + have A5: colorYBBY x n x = colorYBBY x n (x+n). apply lemYBBY5. done. 
      + have mix2: c' = mix (colorYBBY x n x) (colorYBBY x n x). rewrite {2} A5. done. 
      + have CposYel: CposYBBY x (0+n) (mix (colorYBBY x n x) (colorYBBY x n (x+n))). rewrite- mix1. done. 
      + have A6: colorYBBY x n x = yel. rewrite- {2} (addn0 x). apply lemYBBY1. done. 
      + have A7: c' = yel. rewrite A6 in mix2. done. 
      + have A8: CposYBBY x (0+n) yel. rewrite- A7. done. 
      + have A9: yel = red. apply (H_uniq x (0+n)). split. done. done. done. 
Qed.
  
  (* Three_Color_Triangle_Problem_nec_oddB のための定義と補題群 *)
  (* colorBYB x n k z : 最上段の x から x+n までの左端＋右端 3^k 個を青，中央を黄で塗る (範囲外は青にする) *)
  Definition colorBYB (x n k z : nat) := if 3.^k <= z-x <= n-(3.^k) then yel else blu.
  
  (* colorBYB の性質1 *)
  Lemma lemBYB1: forall x y n k i: nat, (0 <= i <= (3.^k).-1) -> colorBYB x n k (x+i) = blu.
  Proof.
    move=> x y n k i range.
    - have T: (colorBYB x n k (x+i) = if 3.^k <= i <= n-(3.^k) then yel else blu).
      by rewrite- {2 3} (x_plus_y_minus_x_is_y x i). 
    - have H: (3 .^ k <= i <= n - 3 .^ k) = false.
      apply/eqP.
      rewrite eq_false. rewrite eq_dual_and. rewrite ! eq_dual_le.
      apply/orP. left. move: range. move/andP. move=> [A B].
      have H1: (0 < 3.^k) = true. by apply expn3Pos.
      by rewrite- eq_adjoint_S_P_le in B. 
    - by rewrite H in T.
  Qed.

  (* colorBYB の性質2 *)
  Lemma lemBYB2: forall x y n k i: nat, (3.^k <= i <= n-(3.^k)) -> colorBYB x n k (x+i) = yel.
  Proof.
    move=> x y n k i range.
    - have T: (colorBYB x n k (x+i) = if 3.^k <= i <= n-(3.^k) then yel else blu).
      rewrite- {2 3} (x_plus_y_minus_x_is_y x i). done.
    - by rewrite range in T.
  Qed.

  (* colorBYB の性質3 *)
  Lemma lemBYB3: forall x y n k i: nat, ((n-(3.^k)).+1 <= i <= n) -> colorBYB x n k (x+i) = blu.
  Proof.
    move=> x y n k i range.
    - have T: (colorBYB x n k (x+i) = if 3.^k <= i <= n-(3.^k) then yel else blu).
      rewrite- {2 3} (x_plus_y_minus_x_is_y x i). done. 
    - have H: (3 .^ k <= i <= n - 3 .^ k) = false.
      apply/eqP.      
      rewrite eq_false. rewrite eq_dual_and. rewrite ! eq_dual_le.
      apply/orP. right. move: range. move/andP. move=> [A B]. done.
    - by rewrite H in T.
  Qed.

  (* n の範囲条件から導かれる不等式 *)
  Lemma fromRangeN:
    forall k n : nat,
      ((3.^k).*2 + 1 <= n < (3.^(k.+1))) -> ((3.^k) <= n) /\ ((3.^k).*2 <= n) /\ (n - (3.^k).*2 <= (3.^k).-1).
  Proof.
    move => k n. move/andP. move=> [rangeN1 rangeN2]. split. 
    - (* first goal *)
      have X1: ((3.^k) <= (3.^k).*2 + 1).
      rewrite- addnn. rewrite eq_assoc_plus. rewrite- eq_le_plus_l. by apply leq0n.
      by apply (trans_lelele X1).
    - (* second goal *)
      have X2: ((3.^k).*2 <= n). 
      apply ltnW. rewrite  addn1 in rangeN1. done.
      split. done. 
    - (* third goal *)
      have X3: (0 < 3.^k) = true. by apply expn3Pos.
      rewrite- (eq_adjoint_S_P_le (n - (3 .^ k).*2)).
      rewrite eq_adjoint_minus_plus_lt.
      rewrite expnS in rangeN2.        
      rewrite (mulnDr' 1 2 (3.^k)) in rangeN2.
      rewrite mul2n in rangeN2.
      rewrite mul1n in rangeN2. done. done. done. 
  Qed.

  Lemma LongOddA:
    forall Cpos:nat->nat->Color->Prop,forall x n k : nat,
        ((3.^k).*2 + 1 <= n < (3.^(k.+1)))
        -> C_exists Cpos
        -> C_mix Cpos
        -> C_uniq Cpos
        -> (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle Cpos x1 y1 (3 .^ k) c0 c1 c2) 
        ->(forall i: nat,(0 <= i <= n -> Cpos (x+i) 0 (colorBYB x n k (x+i)))) 
        -> (
          (forall i: nat,(0 <= i <= n - (3.^k).*2 -> Cpos (x+i) (3.^k) red))
          /\
          (forall i: nat,(3.^k <= i <= n - 3.^k -> Cpos (x+i) (3.^k) red))
        ).
  Proof.
    - move=> Cpos x n k rangeN H_exists H_mix H_uniq triangle topcolor.
      + have A1: (3.^k) <= n. by apply fromRangeN. 
      + have A2: (3 .^ k).*2 <= n. by apply fromRangeN.
      + have A3: n - (3.^k).*2 <= (3.^k).-1. by apply fromRangeN.
      + have exp3Pos: (0 < 3.^k) = true. by apply expn3Pos.    
        split.
      + (* first part *)
        move=> i. move /andP. move => [C D].
      + have E: 0 <= i <= n.
        apply /andP. split. done.
        apply (trans_lelele D), leq_subr.
      + have A4: 0 <= i <= (3.^k).-1.
        apply/andP. split. done. apply (trans_lelele D A3).
      + have CposB: Cpos (x+i) 0 blu. 
        ++ have colB: colorBYB x n k (x+i) = blu. apply (lemBYB1 x 0 n k i A4).
        ++ rewrite- colB. by apply topcolor.            
      + have CposY: Cpos (x+(3.^k)+i) 0 yel.
        ++ have A5: 3.^k <= (3.^k)+i <= n-(3.^k).
           apply /andP. split. by rewrite- eq_le_plus_l.
           rewrite- (eq_adjoint_plus_minus_le ((3.^k)+i) A1).
           rewrite eq_comm_plus. rewrite- eq_assoc_plus. rewrite addnn.
           rewrite eq_comm_plus. rewrite eq_adjoint_plus_minus_le. done. done.
        ++ have A6: 0 <= 3 .^ k + i. apply ltnW. move:A5. move/andP. move=>[A5a A5b]. apply (trans_ltlelt exp3Pos). done. 
        ++ have A7: 3 .^ k + i <= n. move:A5. move/andP. move=>[A5a A5b]. apply (trans_lelele A5b). apply leq_subr. 
        ++ have colY: colorBYB x n k (x+(3.^k)+i) = yel. rewrite eq_assoc_plus. apply (lemBYB2 x 0 n k ((3.^k)+i) A5).
        ++ rewrite- colY. rewrite- addnA. apply topcolor. done. 
      + have CposR: Cpos (x+i) (3.^k) red.
        have mixR: red = mix blu yel. done. 
        rewrite mixR. rewrite- [(3 .^ k)]addn0. rewrite [(3.^k + 0)]addnC.
        apply Bottom_color_of_triangle. done. done. done.
        rewrite eq_assoc_plus. rewrite (eq_comm_plus i (3.^k)). rewrite- eq_assoc_plus. done. done.
      + (* second part *)
        move=> i. move /andP. move => [C D].      
      + have E: 0 <= i <= n.
        apply /andP. split. done.
        apply (trans_lelele D), leq_subr.
      + have A4: 3.^k <= i <= n-(3.^k).
        apply/andP. split. done. done.
      + have CposY: Cpos (x+i) 0 yel.
        ++ have colY: colorBYB x n k (x+i) = yel. apply (lemBYB2 x 0 n k i A4). 
        ++ rewrite- colY. by apply topcolor. 
      + have CposB: Cpos (x+(3.^k)+i) 0 blu.
        ++ have X: n < 3 .^ k.+1. move: rangeN. move/andP. move=>[rangeN1 rangeN2]. done.
        ++ have Y: i <= n - 3 .^ k. done.
        ++ have Z: (3.^k) + i <= n. rewrite eq_comm_plus. rewrite eq_adjoint_plus_minus_le. done. done. 
        ++ have A5: n - 3 .^ k < 3 .^ k + i <= n. 
           apply /andP. split.
           rewrite eq_adjoint_minus_plus_lt. 
           rewrite (eq_comm_plus (3.^k) i). rewrite eq_assoc_plus. rewrite addnn. 
           apply (trans_lelele X). rewrite expnS.
           rewrite (mulnDr' 1 2 (3.^k)). rewrite mul2n. rewrite mul1n.
           rewrite- eq_mono_plus_le_plus. done. done. done. 
        ++ have colB: colorBYB x n k (x+(3.^k)+i) = blu.
           rewrite eq_assoc_plus. apply (lemBYB3 x 0 n k ((3.^k)+i)). done.
        ++ rewrite- colB. rewrite- addnA. by apply topcolor.
      + have CposR: Cpos (x+i) (3.^k) red.
        have mixR: red = mix yel blu. done. rewrite mixR.
        rewrite- [(3.^k)]addn0. rewrite [(3.^k + 0)]addnC.
        apply Bottom_color_of_triangle. done. done. done. 
        rewrite eq_assoc_plus. rewrite (eq_comm_plus i (3.^k)).
        rewrite- eq_assoc_plus. done. done.
  Qed.
  
  Lemma LongOddB:
    forall Cpos:nat->nat->Color->Prop,forall x n k : nat,
        ((3.^k).*2 + 1 <= n < (3.^(k.+1)))
        -> C_exists Cpos
        -> C_mix Cpos
        -> C_uniq Cpos
        -> (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle Cpos x1 y1 (3 .^ k) c0 c1 c2)
        -> (forall i: nat,(0 <= i <= n -> Cpos (x+i) 0 (colorBYB x n k (x+i))))
        -> forall i:nat, (0 <= i <= n-(3.^k).*2) -> Cpos (x+i) ((3.^k).*2) red.
  Proof.
    - move=> Cpos x n k rangeN H_exists H_mix H_uniq triangle color i rangeI.
      + have A1: (3.^k) <= n. by apply fromRangeN. 
      + have A2: (3 .^ k).*2 <= n. by apply fromRangeN.
      + have A3: n - (3.^k).*2 <= (3.^k).-1. by apply fromRangeN.
      + have exp3Pos: (0 < 3.^k) = true. by apply expn3Pos.    
      + have [fromA1 fromA2]: 
          (forall i: nat,(0 <= i <= n - (3.^k).*2 -> Cpos (x+i) (3.^k) red))
          /\ (forall i: nat,(3.^k <= i <= n - 3.^k -> Cpos (x+i) (3.^k) red)). by apply LongOddA.
      + have CposR1: Cpos (x+i) (3.^k) red.
        apply fromA1. done.
      + have CposR2: Cpos (x+i) ((3.^k).*2) red.
      + have mixR: red = mix red red. done.
      + rewrite mixR. rewrite- addnn. rewrite- [(3.^k + 3.^k)]addn0.
        rewrite [_+0]addnC. rewrite- (eq_assoc_plus 0 (3.^k) (3.^k)).
        apply Bottom_color_of_triangle. done. done. done. 
        rewrite (eq_assoc_plus x i (3.^k)). apply fromA2.
        apply /andP. rewrite- (eq_le_plus_r (3.^k) i). split. done.
        rewrite- (eq_adjoint_plus_minus_le (i+3.^k) A1).
        rewrite eq_assoc_plus. rewrite addnn.
        move:rangeI. move/andP. move =>[P Q].
        rewrite (eq_adjoint_plus_minus_le i A2). done. done.
  Qed.
  
  Lemma LongOddC:
    forall Cpos:nat->nat->Color->Prop,forall x n k : nat,
        ((3.^k).*2 + 1 <= n < (3.^(k.+1)))
        -> C_exists Cpos
        -> C_mix Cpos
        -> C_uniq Cpos
        -> (forall i: nat,(0 <= i <= n -> Cpos (x+i) 0 (colorBYB x n k (x+i))))                 
        -> (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle Cpos x1 y1 (3 .^ k) c0 c1 c2)
        -> Cpos x n red.
  Proof.
    - move=> Cpos x n k rangeN H_exists H_mix H_uniq H_BYB triangle.
      + have rangeN1: (3 .^ k).*2 <= n. by apply fromRangeN.
      + have fromB: forall i:nat, (0 <= i <= n-(3.^k).*2 -> Cpos (x+i) ((3.^k).*2) red).
        apply LongOddB. done. done. done. done. done. 
        move=> i rangeI. by apply H_BYB.
      + have fromRR: Cpos x (0 + (3 .^ k).*2 + (n - (3 .^ k).*2)) red.
        apply (AllRed Cpos x ((3.^k).*2) (n-((3.^k).*2))). done. done. done. 
        rewrite eq_assoc_plus in fromRR.
        rewrite (addnBA ((3.^k).*2) rangeN1) in fromRR.
        rewrite x_plus_y_minus_x_is_y in fromRR. done. 
  Qed.

  (* 奇数の場合-2 終わり *)
  Lemma Three_Color_Triangle_Problem_nec_LongOdd :
    forall (x n k : nat), ((3.^k).*2 + 1 <= n < (3.^(k.+1))) -> ~(WellColoredTriangle x n). 
  Proof.
    - move=> x n k rangeN triangle.
      have H_CposBYB: exists Cpos' : nat -> nat -> Color -> Prop,C_uniq Cpos' /\ C_exists Cpos' /\ C_mix Cpos' /\ (forall x0 i : nat, Cpos' (x0 + i) 0 (colorBYB x n k (x0 + i))). apply (C_paint' (colorBYB x n k)).
      move:H_CposBYB.  case=> CposBYB [H_uniq [H_exists [H_mix H]]].
      specialize (triangle CposBYB H_uniq H_exists).
      have topcolor : forall i : nat, ((0 <= i <= n) -> CposBYB (x+i) 0 (colorBYB x n k (x+i))).
      move=>i range. apply H.       
      + move: (rangeN). move/andP. case=>[K1 K2].
      + have tri3k: forall x y: nat, forall c0 c1 c2: Color, Triangle CposBYB x y (3.^k) c0 c1 c2.
        move=> x1 y1 c0 c1 c2. apply Three_Color_Triangle_Problem_suf''.
        exists k. done. done. done. 
      + have fromCpaint: forall i:nat,0<=i<=n -> CposBYB (x+i) 0 (colorBYB x n k (x+i)).
        move=> i rangeI. done.
      
      + have A1: (3.^k) <= n. by apply fromRangeN.
      + have H_CposBYB: forall i:nat, 0<=i<=n -> CposBYB (x+i) 0 (colorBYB x n k (x+i)).
        move=> i rangeI. by apply fromCpaint. 
      + have CposR: CposBYB x n red. by apply (LongOddC CposBYB x n k).
      + have triBYB: Triangle CposBYB x 0 n (colorBYB x n k x) (colorBYB x n k (x+n)) red. apply triangle. done.
        rewrite- {1 3} (addn0 x).  by apply fromCpaint. done. done. 
      + have colB1: colorBYB x n k x = blu.
        rewrite- {2} (addn0 x). 
        apply (lemBYB1 x 0). done. 
      + have colB2: colorBYB x n k (x+n) = blu.
        apply (lemBYB3 x 0). apply/andP. split. 
        rewrite (eq_adjoint_minus_plus_lt n A1).
        rewrite- eq_lt_plus_l. apply expn3Pos. done. 
      + have triBBR: Triangle CposBYB x 0 n blu blu red.
        rewrite- {1} colB1. rewrite- {1} colB2. done.
      + have CposB1: CposBYB x 0 blu.
        rewrite- colB1. rewrite- {1 3} (addn0 x). apply H_CposBYB. done. 
      + have CposB2: CposBYB (x+n) 0 blu.
        rewrite- colB2. apply H_CposBYB. apply/andP. done. 
      + have mixRBB: red = mix blu blu.
        apply triBBR. split. done. done. done.         
  Qed.
    
  Lemma Three_Color_Triangle_Problem_nec' :
    forall (n x : nat), n > 0 -> ~(exists k :nat, n = 3 .^ k) -> ~(WellColoredTriangle x n). 
  Proof.
    rewrite /WellColoredTriangle.
    move=> n x NotZeroN_hyp Notexp3k WCT.
    case (rangeN4 n) => k rangeN. case rangeN => [ZeroN|NotZeroN].
    - rewrite ZeroN in NotZeroN_hyp. done.
    - case (odd_or_even n) => [OddN|EvenN].
      + case NotZeroN => [Is3k|Not3k].
        have Isexp3k: exists k:nat,n=3.^k. by exists k. done.
      + case Not3k => [Short|Long].
        * move:(Short). move/andP. case=>[Short1 Short2].
        * apply (Three_Color_Triangle_Problem_nec_ShortOdd x n k).
          rewrite Short2. rewrite OddN. 
          apply /andP. rewrite Short1. done.
          move=> Cpos  H_uniq H_exists H_mix c c0 c1 Cpos0 Cpos1 [Cpos2a [Cpos2b Cpos2c]]. rewrite add0n in Cpos2c. 
          specialize (WCT Cpos). by apply WCT. 
        * by apply (Three_Color_Triangle_Problem_nec_LongOdd x n k). 
      + apply (Three_Color_Triangle_Problem_nec_even x n).
        rewrite NotZeroN_hyp. by rewrite EvenN. apply WCT.
  Qed.

bbbbbbbbbbbbbbbbbbbbbbbbbb

  
  Theorem Three_Color_Triangle_Problem_nec :
    forall (n x : nat), n > 0 -> (WellColoredTriangle x n) -> (exists k :nat, n = 3 .^ k).
  Proof.
    move=> n x NotZeroN_hyp; apply Contraposition; move=> Notexp3k.
    by apply Three_Color_Triangle_Problem_nec'.
  Qed.

  Theorem Three_Color_Triangle_Problem_sufnec :
    forall (n x : nat) , n > 0 -> (exists k : nat, n = 3 .^ k) <-> (WellColoredTriangle x n). 
  Proof.
    move=> n x NotZeroN. split.
    - by apply Three_Color_Triangle_Problem_suf.
    - by apply Three_Color_Triangle_Problem_nec.
  Qed.
  
  Theorem Three_Color_Triangle_Problem  :
    forall (n : nat) , n > 0 -> (exists k : nat, n = 3 .^ k) <-> (WellColoredTriangle 0 n). 
  Proof.
    move=> n.
    by apply (Three_Color_Triangle_Problem_sufnec n 0).
  Qed.

End Three_Color_Triangle_Problem.







Section Three_Color_Triangle_Problem_modify.
  (* 前節までの述語 Cpos: nat->nat->Color->Prop を関数 cpos nat->nat->Color に置き換えて定理を示す *)
  (* Cpos に関する条件 C_uniq と C_exists は「Cpos が関数的」であることを意味しているので，実際の関数にする *)
  (* この変更により C_uniq と C_exists を落とした形の主張に変更できる *)
  (* C_mix は色塗りに関する要件なので，関数 cpos でもそれに相当する条件 F_mix は必要 *)
  (* 方針 *)
  (* - Cpos+C_uniq+C_exists から cpos+F_mix を作るには choice を用いる *)
  (* - cpos から Cpos+C_uniq+C_exists から を作るには choice を用いる *)  

  Definition F_mix (cpos:nat->nat->Color) := forall x y:nat, (cpos x (y.+1)) = mix (cpos x y) (cpos (x.+1) y). 

  (* (x,y) (x+n,y) (x,y+n) の3頂点の色が mix になっている *)
  Definition TriangleF cpos x y n := (cpos x (y+n)) = mix (cpos x y) (cpos (x+n) y). 

  (* (x,0) から始まる n 段の三角形に要請通りの任意の色塗りをしても 3頂点(x,0),(x+n,0),(x,n)の色は調和している *)
  Definition WellColoredTriangleF x n := forall cpos: nat->nat->Color, F_mix cpos -> TriangleF cpos x 0 n.

  (* cpos から Cpos を作る補題 *)
  Lemma make_Cpos_from_cpos :
    forall cpos:nat->nat->Color,
      F_mix cpos
      -> exists Cpos:nat->nat->Color->Prop,
        C_uniq Cpos /\ C_exists Cpos /\ C_mix Cpos /\ 
        forall y x:nat, Cpos x y (cpos x y). 
  Proof.
    move=>cpos H_mix.
    exists (CposF (fun x=> cpos x 0)).
    - split. (* C_uniq *)   rewrite/C_uniq. apply C_uniq_F. 
    - split. (* C_exists *) rewrite/C_exists. apply C_exists_F. 
    - split. (* C_mix *)    rewrite/C_mix. move=> x y. rewrite !addn1. apply (C_mix_F (fun x=> cpos x 0) x y).
    - move=> y. 
      induction y. done. move=>x. rewrite/CposF in IHy. rewrite/CposF. rewrite H_mix. rewrite IHy. rewrite IHy. done.
  Qed.

  Theorem unique_choice2 :
    forall (A B C:Type) (R:A -> B -> C -> Prop),
      (forall x:A, forall y:B, exists! z : C, R x y z) ->
      (exists f:A->B->C, forall x:A, forall y:B, R x y (f x y)).
  Proof.
    move=>A B C R H.
    have H1: exists R1:A*B -> C -> Prop, forall a:A, forall b:B, forall c:C, R1 (a,b) c <-> R a b c.
    exists (fun w => R w.1 w.2). done. move:H1=>[R'] H2.
    - have [g H3]: exists g:A*B -> C, forall ab:A*B, R' ab (g ab). apply unique_choice.
      move=>ab. specialize (H ab.1 ab.2). apply unique_existence in H.
      move:H=>[[c J1] J2]. exists c. specialize (H2 ab.1 ab.2). rewrite/unique. split.
      rewrite- surjective_pairing in H2. by apply/H2. rewrite /uniqueness in J2. 
      move=>c1 K2. apply J2. done. apply H2. rewrite- surjective_pairing. done.
    - exists (fun a b=>g (a,b)). move=>a b. apply H2. done. 
  Qed.
  
  
  (* Cpos から cpos を抽出する補題 (choice が必要) *)
  Lemma extract_cpos_from_Cpos :
    forall Cpos:nat->nat->Color->Prop,
      C_uniq Cpos
      -> C_exists Cpos
      -> C_mix Cpos                 
      -> exists cpos:nat->nat->Color, (forall x y:nat, Cpos x y (cpos x y)) /\ F_mix cpos.
  Proof.
    move=>Cpos H_uniq H_exists H_mix.
    - have [cpos H]: exists cpos:nat->nat->Color, (forall x y:nat, Cpos x y (cpos x y)). apply unique_choice2. move=>x y.
      rewrite/C_uniq in H_uniq. rewrite/C_exists in H_exists.
      specialize (H_uniq x y). specialize (H_exists x y). move:H_exists=>[c H_exists].
      exists c. rewrite/unique. split. done. move=>c' H. apply H_uniq. split. done. done.
    - exists cpos. split. done. rewrite /F_mix. move=>x0 y0.
      apply (H_mix x0 y0). split. done. split. rewrite addn1. done. rewrite addn1. done. 
  Qed.

  (* 2つの Triangle は同値である *)
  Lemma Triangle_equiv:
    forall Cpos:nat->nat->Color->Prop, forall cpos:nat->nat->Color, 
        (forall x y:nat, Cpos x y (cpos x y))
        -> forall x y n:nat, Triangle Cpos x y n (cpos x y) (cpos (x+n) y) (cpos x (y+n)) <-> TriangleF cpos x y n.
  Proof.
    move=>Cpos cpos H x y n. split.
    - move=>tri. apply tri. split. done. split. done. done. 
    - move=>triF K. done. 
  Qed.
  
  
  (* 2つの WellColoredTriangle は同値である *)
  Lemma WCTequiv: forall x n:nat, WellColoredTriangleF x n <-> WellColoredTriangle x n.
  Proof.
    move=>x n. split.
    - move=>H. rewrite/WellColoredTriangle. rewrite/WellColoredTriangleF in H.
      move=>Cpos H_uniq H_exists H_mix c2 c0 c1 H2 H3 H4.
      have [cpos [K1 K2]]: exists cpos:nat->nat->Color, (forall x y:nat, (Cpos x y (cpos x y))) /\ F_mix cpos.
      apply extract_cpos_from_Cpos. done. done. done.
      specialize (H cpos K2).
      have J0: c0 = cpos x 0. apply (H_uniq x 0). done.       
      have J1: c1 = cpos (x+n) 0. apply (H_uniq (x+n) 0). done.
      have J2: c2 = cpos x n. apply (H_uniq x n). done. 
      rewrite J0. rewrite J1. rewrite J2. done. 
    - move=>H. rewrite/WellColoredTriangleF. rewrite/WellColoredTriangle in H.
      move=>cpos H_fmix. 
      have [Cpos [H_uniq [H_exists [H_mix H1]]]]: exists Cpos:nat->nat->Color->Prop, C_uniq Cpos /\ C_exists Cpos /\ C_mix Cpos /\ forall y x:nat, Cpos x y (cpos x y).
      apply make_Cpos_from_cpos. done.
      rewrite/TriangleF. rewrite add0n.
      specialize (H Cpos H_uniq H_exists H_mix (cpos x n) (cpos x 0) (cpos (x+n) 0)). apply H.
      done. done. done. done. 
  Qed.

  (* 終わり *)
  Theorem Three_Color_Triangle_Problem2  :
    forall (n : nat) , n > 0 -> (exists k : nat, n = 3 .^ k) <-> (WellColoredTriangleF 0 n). 
  Proof.
    move=> n H. split. move=>K. apply/WCTequiv. by apply Three_Color_Triangle_Problem.
    move/WCTequiv. by apply Three_Color_Triangle_Problem.
  Qed.
  

End Three_Color_Triangle_Problem_modify.
