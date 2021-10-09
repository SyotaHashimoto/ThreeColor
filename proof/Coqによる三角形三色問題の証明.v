Require Import PeanoNat Le Lt Plus Mult Even.
From mathcomp
     Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import MyRewrite.

Section nat1.

  Lemma x_plus_y_minus_x_is_y: forall x y : nat, x + y - x = y.
  Proof.
    move=> x y.
    have G1: x + y = y + x. apply Nat.add_comm.
    rewrite G1. rewrite- addnBA.
    have G2: x-x = 0. apply Nat.sub_diag.
    rewrite G2. apply Nat.add_0_r. done. 
  Qed.

  Lemma expn3Pos : forall m, 0 < 3^m .
  Proof. move=> m. rewrite expn_gt0; apply/orP; by left. Qed.
  
  Lemma odd_or_even : forall n : nat, odd n \/ odd n = false.
  Proof.
    elim=> [ | n IHn].
    - right. done.
    - case IHn => [Odd|Even].
      + right. by rewrite /= Odd.
      + left.  by rewrite /= Even.
  Qed.

  Lemma connect3m :
    forall n m : nat,
      (3 ^ m <= n /\ n <= (3 ^ m).*2) \/ ((3 ^ m).*2 + 1 <= n /\ n < 3 ^ m.+1) <->
      (3 ^ m <= n /\ n < 3 ^ m.+1).
  Proof.
    move=> n m. split.
    - move=> Long; case Long.
      + move=> []Left1 Left2; split. done.
        rewrite expnS -{1}(addn1 2) mulnDl mul1n -(addn1 n) leq_add. done.
        rewrite mul2n. done.
        rewrite expn_gt0; apply /orP; by left.
      + move=> [] Right1 Right2; split.
        suff : (3 ^ m <= (3 ^ m).*2 + 1).
        move=> tmp. apply (trans_lelele tmp). done.
        have A: 3^m <= (3^m).*2. apply self_double. 
        apply (trans_lelele A). rewrite addn1. done. done.
    - move=> [] Short1 Short2.
      have leq23mOr : forall m1 m2 : nat, (n <= (3^m).*2) \/ ((3^ m).*2 + 1 <= n).
      move=> m1 m2. apply/orP. rewrite addn1.
      have leq_total : forall m n:nat, (m<=n) || (n<m).
      move=>m3 n3.
      rewrite leq_eqVlt -(Bool.orb_diag (m3 == n3)) {2}(eq_sym m3 n3).
      rewrite -(orbA (m3==n3) (n3==m3) (m3<n3)) (orbC (n3==m3) (m3<n3)).
      rewrite orbA -leq_eqVlt -orbA -leq_eqVlt. apply leq_total.
      apply leq_total.
    - case (leq23mOr n m) => [Less|More].
      + left.  split. by []. by [].
      + right. split. by []. by [].
  Qed.

  Lemma nat_total' : forall n : nat, exists k : nat, (n = 0) \/ (3^k <= n <= (3^k).*2) \/ ((3^k).*2 + 1 <= n < (3^(k.+1))).
  Proof.
    elim=> [ | n IHn].
    - exists 0. left. done.
    - move: IHn. case. move=> k IHn.
      case IHn.
      + move=> Zero.
        rewrite Zero. exists 0. rewrite /=. right; left. done.
      (* n.+1 = 1 と n.+1 > 1 で場合分け *)
      ++ have case1 : forall n : nat, n.+1 = 1 \/ n.+1 > 1.
         elim=> [ | n1 IHn1].
         * left. by [].
         * case IHn1 => H0.
           ** rewrite H0. by right.
           ** right; apply /ltP; apply le_S; by apply /ltP.
      + case (case1 n) => [Zero|NotZero].      
        (* n.+1 = 1 のとき *)
        * rewrite Zero. exists 0. right; left. by rewrite /=.
        (* n.+1 > 1 のとき *)
        * have Short1 : forall n k : nat, 3 ^ k <= n <= (3 ^ k).*2 <-> (3 ^ k <= n /\ n <= (3 ^ k).*2).
          move=> n0 k0; split => [H | H]. by apply /andP. by apply /andP.
          have Long1 : forall n k : nat, (3 ^ k).*2 + 1 <= n < 3 ^ k.+1 <-> (3 ^ k).*2 + 1 <= n /\ n < 3 ^ k.+1.
          move=> n0 k0; split => [H | H]. by apply /andP. by apply /andP.
          rewrite Short1 Long1 connect3m. move /andP. move => rangeN.
          have Short2 : forall n k : nat, 3 ^ k <= n.+1 <= (3 ^ k).*2 <-> (3 ^ k <= n.+1 /\ n.+1 <= (3 ^ k).*2).
          move=> n0 k0; split => [H | H]. by apply /andP. by apply /andP.
          have Long2 : forall n k : nat, (3 ^ k).*2 + 1 <= n.+1 < 3 ^ k.+1 <-> (3 ^ k).*2 + 1 <= n.+1 /\ n.+1 < 3 ^ k.+1.
          move=> n0 k0; split => [H | H]. by apply /andP. by apply /andP.
          have Boundary : forall n k : nat, (n.+1 = 3 ^ k.+1) <-> (n.+1 == 3 ^ k.+1).
          move=> n0 k0. split => [H | H]. by apply /eqP. by apply /eqP.
          (* n.+1 = 3 ^ k と n.+1 < 3 ^ k.+1で場合分け *)
          have rangeBoundary : (n.+1 = 3 ^ k.+1) \/ (n.+1 < 3 ^ k.+1).
          move: rangeN. move /andP; move=> [] ranegeN1 rangeN2.
          rewrite Boundary. apply /orP. by rewrite leq_eqVlt in rangeN2.
          case rangeBoundary => [rangeN1|rangeN2].
          (* n.+1 = 3 ^ k のとき *)
          ** exists (k.+1). rewrite rangeN1. right; left.
             apply /andP. split. done.
             rewrite- addnn. rewrite- {1} (add0n (3^k.+1)). rewrite- eq_mono_plus_le_plus. done. 
          ** exists k. rewrite Short2 Long2 connect3m. right. split. move: rangeN.
             move /andP. move=> [] range1 range2. by apply leqW. by [].
  Qed.        

  Lemma nat_total : forall n : nat, exists k : nat, (n = 0) \/ (n = 3^k) \/ (3^k < n <= (3^k).*2) \/ ((3^k).*2 + 1 <= n < (3^(k.+1))).
  Proof.
    move=> n.
    have [k H]: exists k:nat, (n = 0) \/ (3^k <= n <= (3^k).*2) \/ ((3^k).*2 + 1 <= n < (3^(k.+1))).
    apply nat_total'. exists k.
    suff K: ((n = 3 ^ k) \/ (3 ^ k < n <= (3^k).*2)) <-> (3^k <= n <= (3^k).*2).
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
      destruct L1. move/eqP in H0. rewrite H0. by left. rewrite H0. by right.
  Qed.
 
End nat1.

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
  
  Lemma mixCut (c0 c1 c2 c3 : Color) :
    mix ( mix (mix c0 c1) (mix c1 c2) ) ( mix (mix c1 c2) (mix c2 c3) ) = mix c0 c3.
  Proof. case c0, c1, c2, c3; by rewrite /=. Qed.

  (* ----- 色づけ関数のリフト (最上段のみ色塗りから全域への色塗りに拡張する) ----- *)
  (* ----- 後に定義する colorYBBY や colorBYB などに対して適用する ----- *)  
  Fixpoint F (color : nat -> Color) (x y : nat) : Color :=
    match y with
    | 0 => color x
    | y'.+1 => mix (F color x y') (F color(x.+1) y')
    end.
  
  (* ----- リフトして作った色塗り関数は F_mix を満たす ----- *)  
  Lemma cposF: forall color:nat->Color, F_mix (F color).
  Proof. move=>color x y. apply/ceqP. done. Qed.
  
  (* ----- 三角形三色問題 ----- *)
  Lemma Three_Color_Triangle_Problem_suf' :
    forall cpos: nat->nat->Color, forall (k n x y : nat), 
        n = 3 ^ k
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
      + have Triangle035 : TriangleF cpos x y (3^k). by apply IHk.
      + have Triangle346 : TriangleF cpos (x+3^k) y (3^k). by apply IHk.
      + have Triangle417 : TriangleF cpos (x+(3^k).*2) y (3^k). by apply IHk.
      + have Triangle568 : TriangleF cpos x (y+3^k) (3^k). by apply IHk.
      + have Triangle679 : TriangleF cpos (x+3^k) (y+3^k) (3^k). by apply IHk.
      + have Triangle892 : TriangleF cpos x (y+(3^k).*2) (3^k). by apply IHk.
      + rewrite /TriangleF.
        rewrite- (mixCut (cpos x y) (cpos (x+3^k) y) (cpos (x+(3^k).*2) y) (cpos (x+n) y)).
        rewrite /TriangleF in Triangle035.
        move:Triangle035; move/ceqP; move=>Triangle035; rewrite- Triangle035. 
        rewrite- !addnn. rewrite addnA.
        move:Triangle346; move/ceqP; move=>Triangle346; rewrite- Triangle346.
        move:Triangle568; move/ceqP; move=>Triangle568; rewrite- Triangle568.
        rewrite Step.
        have add23n3n : 3 ^ k.+1 = (3 ^ k).*2 + 3 ^ k.
        rewrite expnS  (mulnDl 1 2) mul1n mul2n addnC; done.
        rewrite add23n3n -!addnA addnn !addnA.
        move:Triangle417; move/ceqP; move=>Triangle417; rewrite- Triangle417.
        rewrite- addnn. rewrite! addnA. 
        move:Triangle679; move/ceqP; move=>Triangle679; rewrite- Triangle679.
        rewrite- !addnA. rewrite addnn. rewrite !addnA. 
        move:Triangle892; move/ceqP; move=>Triangle892; rewrite- Triangle892.
        rewrite- addnA. rewrite (addnC (3^k) ((3^k).*2)). rewrite !addnA.
        by apply/ceqP.
  Qed.

  Theorem Three_Color_Triangle_Problem_suf'' :
    forall (x y n : nat),
      (exists k : nat, n = 3 ^ k) ->
      forall cpos:nat->nat->Color, F_mix cpos -> TriangleF cpos x y n. 
  Proof.
    move=> x y n Step cpos H_mix. 
    move:Step. case; move=> k Step. 
    by apply (Three_Color_Triangle_Problem_suf' cpos k n x y).
  Qed.

  (* 十分条件 *)
  Theorem Three_Color_Triangle_Problem_suf :
    forall (x n : nat),
      (exists k : nat, n = 3 ^ k) -> (WellColoredTriangleF x n). 
  Proof.
    rewrite /WellColoredTriangleF.
    move=> x n Step cpos H_mix.  
    by apply Three_Color_Triangle_Problem_suf''.    
  Qed.


  
  (* ここから必要条件 ------------------------------------*)

  (* ある段が全て赤ならその下はずっと赤 *)  
  Lemma AllRedN :
    forall cpos:nat->nat->Color, forall x y n : nat,
        F_mix cpos        
        -> (forall i :nat, (0 <= i <= n -> red = cpos (x+i) y))
        -> forall q p : nat, (0 <= p+q <= n ->  red = cpos (x+p) (y+q)).
  Proof.
    move=> cpos x y n H_mix topcolor.
    induction q.
    - (* base case: q is 0 *)
      move=> p. rewrite ! addn0. apply topcolor. 
    - (* induction case: q is successor *)
      move=> p. move/andP. move =>[rangePQ1 rangePQ2].
      + have prevL: red = cpos (x+p) (y+q).
        apply IHq.
        apply /andP. split. done.
        rewrite addnS in rangePQ2. by apply ltnW. 
      + have prevR: red = cpos ((x+p).+1) (y+q).
        rewrite- (addnS x p). 
        apply IHq. apply /andP. split. done. 
        rewrite addSn. rewrite addnS in rangePQ2. done.
    - rewrite /F_mix in H_mix. specialize (H_mix (x+p) (y+q)). move:H_mix; move/ceqP; move=>H_mix.
      rewrite addnS. rewrite- prevL in H_mix. rewrite- prevR in H_mix. rewrite H_mix. done. 
  Qed.

  (* ある段が全て赤なら最下段も赤 *)
  Lemma AllRed:
    forall cpos:nat->nat->Color, forall x y n : nat,
        F_mix cpos
        -> (forall i :nat, (0 <= i <= n -> red = cpos (x+i) y))
        -> red = cpos x (y+n). 
  Proof.
    move=> cpos x y n H_mix topcolor.
    have fromAllRedN: forall q p : nat, (0 <= p+q <= n ->  red = cpos (x+p) (y+q)).
    apply AllRedN. done. done.
    generalize (fromAllRedN n 0). rewrite addn0. rewrite add0n.
    move=> A. apply A. apply/andP. done. 
  Qed.


  
  (* Begin: Three_Color_Triangle_Problem_nec_even --------------------*)
  (* colorYB x n z : 最上段の x から x+n までのマスを黄，青と交互に塗る (範囲外は黄にする) *)
  Definition colorYB (x n z : nat) :=
    if (0 <= z-x <= n) && (odd (z-x) == false) then yel
    else if (0 <= z-x <= n) && odd (z-x) then blu
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
  Lemma lemYB2: forall x n i: nat, (0 <= i <= n) && odd i -> colorYB x n (x+i) = blu.
  Proof.
    move=> x n i.
    move /andP. move=> [] range. move=> [] oddI.
    rewrite- (x_plus_y_minus_x_is_y x i) in range.
    rewrite- (x_plus_y_minus_x_is_y x i) in oddI.
    rewrite /colorYB. rewrite range oddI. by rewrite /=.
  Qed.
  
  (* colorYB の性質3 *)
  Lemma lemYB3: forall x n : nat, (odd n == false) -> colorYB x n x = colorYB x n (x+n).
  Proof.
    move=> x n. move /eqP => oddN.
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
    forall cpos:nat->nat->Color, forall x n : nat,
        n > 0
        -> F_mix cpos
        -> (forall i : nat, (0<=i<=n -> cpos (x+i) 0 = colorYB x n (x+i)))
        -> (forall i : nat, (0<=i<=n.-1 -> cpos (x+i) 1 = red)).
  Proof.
    move=> cpos x n Notzero H_mix topcolor i rangeI.
    
    (* 最上段のマスが colorYB で塗られていることを示す *)
    - have rangetop1 : 0 <= i <= n. apply /andP; split.
      + by [].
      + move: rangeI; move /andP => [] rangetop1a rangetop1b.
        apply (leq_trans rangetop1b); apply leq_pred.
      + generalize (topcolor i) => Cpos1; specialize (Cpos1 rangetop1).
    - have rangetop2 : 0 <= i.+1 <= n. apply /andP; split.
      + by [].
      + move: rangeI; move /andP => [] rangetop2a rangetop2b.
        apply (leq_ltn_trans rangetop2b). rewrite ltn_predL; done.
      + generalize (topcolor (i.+1)) => Cpos2; specialize (Cpos2 rangetop2).
        rewrite- {1}addn1 addnA in Cpos2; rewrite addn1 in Cpos2.

    (* 最上段より 1 段下のマスの色は mix と colorYB で得られることを示す *)
    - have Cpos3 : cpos (x+i) 1 = mix (cpos (x + i) 0) (cpos (x + i).+1 0).
      apply /ceqP; apply (H_mix (x+i) 0); done.

    (* colorYB で塗られている色を求める *)
    - case (odd_or_even i) => [OddI|EvenI].
      (* i が奇数のとき *)
      + have Color1 : colorYB x n (x + i) = blu.
        apply lemYB2; by rewrite rangetop1 OddI.
      + have Color2 : colorYB x n (x+i.+1) = yel.
        have OddI1 : odd (i.+1) = false. by rewrite /= OddI.
        apply lemYB1; by rewrite /colorYB rangetop2 OddI1.
      + rewrite Color1 in Cpos1; rewrite Color2 in Cpos2.
        rewrite Cpos1 Cpos2 /= in Cpos3; done.
      (* i が偶数のとき *)
      + have Color1 : colorYB x n (x+i) = yel.
        apply lemYB1; by rewrite /colorYB rangetop1 EvenI.
      + have Color2 : colorYB x n (x+i.+1) = blu.
        have OddI1 : odd (i.+1) = true. by rewrite /= EvenI; done.
        apply lemYB2; by rewrite /colorYB rangetop2 OddI1.
      + rewrite Color1 in Cpos1; rewrite Color2 in Cpos2.
        rewrite Cpos1 Cpos2 /= in Cpos3; done.
  Qed.
  
  Lemma EvenB :
    forall cpos:nat->nat->Color, forall x n : nat,
        n > 0
        -> F_mix cpos
        -> (forall i : nat, ((0<=i<=n) -> cpos (x+i) 0 = colorYB x n (x+i)))
        -> (cpos x n = red).
  Proof.
    move=> cpos x n Notzero H_mix topcolor.
    have AllRed' : forall i:nat,(0<=i<=n.-1) -> cpos (x+i) 1 = red. by apply EvenA.
    have cal : n+0 = (0+1)+(n.-1).
    rewrite addnAC addnC -addnA addn1 2!add0n.
    symmetry; apply prednK; done.
    rewrite -[n]addn0 cal; symmetry; apply AllRed. by [].
    move=> i' range; rewrite [0+1]addnC addn0; symmetry; by apply AllRed'. 
  Qed.

  Lemma Three_Color_Triangle_Problem_nec_even :
    forall x n :nat, (n > 0) && (odd n == false) -> ~(WellColoredTriangleF x n).
  Proof.
    move=> x n /andP [] Notzero Even Wct.
    rewrite /WellColoredTriangleF in Wct.
    - have [cposYB[H_mix Paint]] : exists cposYB: nat->nat->Color, F_mix cposYB /\ forall x1 y1: nat, cposYB x1 y1 = F (colorYB x n) x1 y1.
      exists (F (colorYB x n)); split. apply cposF. by [].
    - have Topcolor : forall i : nat, colorYB x n (x+i) = cposYB (x+i) 0.
      move=> i; by rewrite Paint.
      + have A1 : colorYB x n x = cposYB x 0. by rewrite Paint.
      + have A2 : colorYB x n (x+n) = cposYB (x+n) 0. by rewrite Paint.
      + have B1 : colorYB x n x = yel. by rewrite /colorYB subnn /=.
      + have B2 : colorYB x n x = colorYB x n (x+n). by apply lemYB3.
    - specialize (Wct (cposYB)). specialize (Wct H_mix).
      rewrite /TriangleF addnC addn0 -A1 -A2 -B2 B1 /= in Wct.
      have Wct' : cposYB x n = red. by apply EvenB. by rewrite Wct' in Wct.   
  Qed.
  (* End: Three_Color_Triangle_Problem_nec_Even --------------------*)

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
    move /andP. move=> [] range1 range2. rewrite /=. by apply ltn_geF.
    specialize (range_false range). by rewrite range_false /=.    
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
    move /andP. move=> [] range1 range2.
    by apply /andP /andP; rewrite negb_and; apply /orP; left; rewrite- leqNgt.
    specialize (range_false range). by rewrite range_false /=.
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
    move /andP. move=> [] range1 range2. rewrite /=. by apply ltn_geF.
    specialize (range_false range). by rewrite range_false /=.
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
    forall cpos:nat->nat->Color,forall x n k : nat,
        ((3^k < n <= (3^k).*2) && odd n)
        -> F_mix cpos              
        -> (forall(x1 y1:nat), TriangleF cpos x1 y1 (3 ^ k))
        -> (forall i : nat, ((0 <= i <= n) -> (colorYBBY x n (x+i)) = (cpos (x+i) 0)))
        -> (forall i : nat, ((0 <= i <= n - 3^k) -> (colorYB x (n-3^k) (x+i)) = (cpos (x+i) (3^k)))).
  Proof.
    move=> cpos x n k H H_mix.
    move:H. move/andP. case=>[A B]. move:(A). move/andP. case=>[A1 A2]. move=>triangle color i rangeI.
    move: (rangeI). move/andP. case=>[rangeI1 rangeI2].
    - have A3: n < (3^k).*2. rewrite eq_le_eq_lt in A2. move:A2. move/orP. case. move=>P.
      have B': odd ((3^k).*2). move/eqP in P. rewrite- P. done. rewrite odd_double in B'. done. done.
    - have E: 3 ^ k <= n. by apply ltnW.       
    - have C1: 1+(n./2).*2 = n. rewrite- {2} (odd_double_half n). rewrite B. done.
    - have C2: (n./2).*2 = n.-1. apply/eqP. rewrite- eq_adjoint_S_P_eq. apply/eqP. done. by apply odd_gt0.
    - have C3: n-(n./2) = (n./2).+1. apply/eqP. rewrite eq_adjoint_minus_plus_eq. apply/eqP.     
      rewrite- addn1. rewrite eq_comm_plus. rewrite- eq_assoc_plus. rewrite addnn. by rewrite eq_comm_plus.
      apply self_half. 
    - have C4: n./2 < 3^k. by rewrite eq_adjoint_half_double_lt.
    - have C5: n-3^k <= n./2. rewrite eq_adjoint_minus_plus_le. rewrite eq_comm_plus.
      rewrite- eq_adjoint_minus_plus_le. rewrite C3. done. 
    - have C6: i<=n./2. apply (trans_lelele rangeI2). done.
    - have C7: n./2 < i + 3 ^ k. apply (trans_ltlelt C4). rewrite eq_comm_plus. apply leq_addr.
    - have C8: i + 3 ^ k <= n. rewrite eq_adjoint_plus_minus_le. done. done. 
    - have C9: odd (3^k).
      (* 省略可能 *)
      have oddD m1 n1 : odd (m1 + n1) = odd m1 (+) odd n1.
      elim: m1 => [|m IHm1] //=; rewrite -addTb IHm1 addbA addTb. by [].
      have oddM m2 n2 : odd (m2 * n2) = odd m2 && odd n2.
      elim: m2 => //= m2 IHm2; rewrite oddD -addTb andb_addl -IHm2. by[].
      (* -------- *)  
      have oddexpn : forall n3 m3 : nat, odd m3 -> odd (m3 ^ n3).
      elim => [ | n3 IHn3]. by []. move=> m3 Odd.
      rewrite expnS oddM; apply /andP; split. by []. by rewrite IHn3.
      apply oddexpn. by [].
    - have rangeIa: 0 <= i <= n.
      apply/andP; split. done. apply (trans_lelele rangeI2); apply leq_subr.
    - have rangeIb: 0 <= (i+3^k) <= n.
      apply/andP; split. apply (trans_lelele rangeI1); apply leq_addr. rewrite eq_adjoint_plus_minus_le. done. done.
    - have posN: 0<n. by apply odd_gt0.
    - have Cpos1: (colorYBBY x n (x+i)) = (cpos (x+i) 0).
      apply color. apply rangeIa.
    - have Cpos2: (colorYBBY x n (x+i+3^k)) = (cpos (x+i+3^k) 0).
      rewrite eq_assoc_plus. apply color. apply rangeIb.
    - have cpos_mix: cpos (x+i) (3^k)= mix (cpos (x+i) 0) (cpos (x+i+3^k) 0). 
      specialize (triangle (x+i) 0). rewrite /TriangleF in triangle. move:triangle; move/ceqP. done. 
    - have or: odd i || ~~odd i. apply orbN. move/orP in or. case:or=> [oddI|evenI].
      + (* Case of oddI *)
        have blu1: colorYBBY x n (x+i) = blu.
        apply lemYBBY3. apply/andP. split. apply/andP; split. done. by apply (trans_lelele rangeI2). by rewrite oddI.
        have blu2: colorYBBY x n (x+i+3^k) = blu.
        rewrite (eq_assoc_plus x i (3^k)). apply lemYBBY4.
        apply/andP. split. apply/andP; split. rewrite- eq_adjoint_half_double_lt in A3. 
        apply (trans_ltltlt A3). rewrite- {1} (add0n (3^k)). rewrite- eq_mono_plus_lt_plus. by apply odd_gt0. done.
        rewrite eq_odd_plus. by rewrite C9. done.

        have colorYB_is_blu: colorYB x (n-3^k) (x+i) = blu.
        apply lemYB2. rewrite oddI; rewrite rangeI1; rewrite rangeI2. done. 
        rewrite colorYB_is_blu; rewrite cpos_mix; rewrite- Cpos1; rewrite- Cpos2; rewrite blu1; rewrite blu2; done.
      + (* Case of evenI *)
        have yelYBBY1: colorYBBY x n (x+i) = yel.
        apply lemYBBY1. rewrite- eq_false in evenI. rewrite evenI. rewrite rangeI1. rewrite C6. done.
        have yelYBBY2: colorYBBY x n (x+i+3^k) = yel. rewrite- addnA. 
        apply lemYBBY2. rewrite C7. rewrite C8. rewrite eq_even_plus. by rewrite C9. done.        
        have yelYB: colorYB x (n-3^k) (x+i) = yel. apply lemYB1. rewrite rangeI. rewrite- eq_false in evenI. done.
        rewrite yelYB; rewrite cpos_mix; rewrite- Cpos1; rewrite- Cpos2; rewrite yelYBBY1; rewrite yelYBBY2. done.
  Qed.
  
  Lemma ShortOddB :
    forall cpos:nat->nat->Color,forall x n k : nat,
        ((3^k < n <= (3^k).*2) && odd n)
        -> F_mix cpos
        -> (forall(x1 y1:nat), TriangleF cpos x1 y1 (3 ^ k)) 
        -> (forall i : nat, ((0 <= i <= n) -> (colorYBBY x n (x+i)) = (cpos (x+i) 0)))
        -> (forall i : nat, ((0 <= i <= (n - 3^k).-1) -> red = cpos (x+i) ((3^k).+1))).
  Proof.
    move=> cpos x n k cond1 H_mix triangle color i rangeI.
    have H_mix_eq: forall x y:nat, cpos x y.+1 = mix (cpos x y) (cpos x.+1 y). move=>x1 y1; apply/ceqP; done.
    move: (rangeI). move/andP. case=>[C1 C2].
    move: cond1. move/andP. case=>[rangeN oddN]. 
    move:(rangeN). move/andP. case=>[rangeN1 rangeN2].
    have C3: n>0. have D: 0<=3^k. apply leq0n. apply (trans_leltlt D). done.
    have C4 : 0 < n - 3 ^ k. rewrite ltn_subCr. rewrite subn0. done.
    have fromOddA: forall i:nat, (0<=i<=n-3^k -> (colorYB x (n-3^k) (x+i)) = cpos (x+i) (3^k)).
    apply ShortOddA. apply /andP. rewrite oddN. by rewrite rangeN. done. done. done. 
    have rangeI1 : 0 <= i <= n - 3 ^ k. rewrite C1. rewrite (leq_trans C2). done. apply leq_pred. 
    have rangeI2 : 0 <= i.+1 <= n - 3 ^ k. apply (leq_ltn_trans C2). rewrite ltn_predL. done.
    (* 3^k 段下のマスの色は colorYB で塗られていることを示す *)
    have Cpos1 : (colorYB x (n - 3^k) (x + i)) = cpos (x + i) (3 ^ k).
    generalize (fromOddA i) => Cpos1.
    specialize (Cpos1 rangeI1). done.
    have Cpos2 : (colorYB x (n - 3^k) (x + i).+1) = cpos (x + i).+1 (3 ^ k).
    generalize (fromOddA i.+1) => Cpos2.
    specialize (Cpos2 rangeI2).
    rewrite- addnS. done.
    (* 「(x+i,3^k +1) のマスの色は赤」を示すには colorYB の値から mix で計算できる *)
    have Color : red = mix (cpos (x+i) (3^k)) (cpos (x+i).+1 (3^k)).
    (* colorYB で塗られている色を示す．i の偶奇で場合分け *)
    - case (odd_or_even i) => [OddI1|EvenI1].
      (* Case: i is odd *)
      + have Color1 : colorYB x (n - 3 ^ k) (x + i) = blu.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangeI1 OddI1. done.
      + have Color2 : colorYB x (n - 3 ^ k) ((x + i).+1) = yel.
        have OddI2 : odd i.+1 = false. by rewrite /= OddI1.
        rewrite /colorYB. rewrite- addn1. rewrite- addnA.
        rewrite x_plus_y_minus_x_is_y addn1.
        rewrite rangeI2 OddI2. done.
      + rewrite- Cpos1. rewrite Color1. rewrite- Cpos2. rewrite Color2. done.
      (* Case: i is even *)
      + have Color1 : colorYB x (n - 3 ^ k) (x + i) = yel.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangeI1 EvenI1. done.
      + have Color2 :colorYB x (n - 3 ^ k) ((x + i).+1) = blu.
        have OddI2 : odd i.+1 = true. by rewrite /= EvenI1.
        rewrite /colorYB. rewrite- addn1. rewrite- addnA.
        rewrite x_plus_y_minus_x_is_y addn1.
        rewrite rangeI2 OddI2. done.
      + rewrite- Cpos1. rewrite Color1. rewrite- Cpos2. rewrite Color2. done.
    - rewrite Color. done. 
  Qed.
  
  Lemma ShortOddC :
    forall cpos:nat->nat->Color,forall x n k : nat,
        ((3^k < n <= (3^k).*2) && odd n)
        -> F_mix cpos
        -> (forall(x1 y1:nat), TriangleF cpos x1 y1 (3 ^ k))
        -> (forall i : nat, ((0 <= i <= n) -> (colorYBBY x n (x+i)) = (cpos (x+i) 0)))
        -> red = cpos x n. 
  Proof.
    move=> cpos x n k cond H_mix triangle color.
    move: (cond). move/andP. case=>[C1 C2].
    move: C1. move/andP. case=>[rangeN1 rangeN2]. 
    have fromOddB: forall i:nat, 0<=i<=(n-3^k).-1 -> red = cpos (x+i) ((3^k).+1).
    apply ShortOddB. done. done. done. done. 
    have fromAllRed: red = cpos x (((3^k)+1)+((n-3^k)-1)).
    apply AllRed. done. rewrite subn1. rewrite addn1. done.
    have D: 0+n = (0 + 3 ^ k + 1 + (n - 3 ^ k - 1)).
    apply/eqP. rewrite- addnA. rewrite- addnA.  
    rewrite- eq_mono_plus_eq_plus_l. rewrite addnC. 
    rewrite- eq_adjoint_minus_plus_eq. rewrite addnC. 
    rewrite- eq_adjoint_minus_plus_eq. done.
    rewrite- eq_adjoint_plus_minus_lt. rewrite add0n. done.
    apply ltnW. done. 
    rewrite- D in fromAllRed. done. 
  Qed.
  
  Lemma Three_Color_Triangle_Problem_nec_ShortOdd :
    forall x n k : nat, ((3^k < n <= (3^k).*2) && (odd n)) -> ~(WellColoredTriangleF x n).
  Proof.
    move=> x n k cond triangle. rewrite/WellColoredTriangleF in triangle.
    have [cposYBBY [H_mix B]]: exists cposYBBY: nat->nat->Color, F_mix cposYBBY /\ forall x1 y1: nat, cposYBBY x1 y1 = F (colorYBBY x n) x1 y1.
    exists (F (colorYBBY x n)). split. apply cposF. done.
    specialize (triangle cposYBBY H_mix).
    move: (cond). move/andP. case=>[K1 K2].
    + have tri3k: forall x1 y1: nat, TriangleF cposYBBY x1 y1 (3^k).
      move=> x1 y1. apply Three_Color_Triangle_Problem_suf''. exists k. done. done.
    + have A1: (colorYBBY x n x) = cposYBBY x 0. rewrite B. done. 
    + have A2: forall i:nat, (colorYBBY x n (x+i)) = cposYBBY (x+i) 0. move=>i. rewrite B. done.
    + have A5: cposYBBY x 0 = cposYBBY (x+n) 0. rewrite- A1. rewrite- A2. apply lemYBBY5. rewrite K2. done. 
    + have cpos_x_0_yel: cposYBBY x 0 = yel. rewrite- (addn0 x). rewrite- A2. apply lemYBBY1. done.
    + have cpos_xn_0_yel: yel = cposYBBY (x+n) 0. rewrite- A5. done. 
    + have cpos_x_n_yel: yel = cposYBBY x n.
      rewrite /TriangleF in triangle. move:triangle; move/ceqP; move=>triangle.
      rewrite cpos_x_0_yel in triangle. rewrite- cpos_xn_0_yel in triangle. done. 
    + have cpos_x_n_red: red = cposYBBY x n. 
      apply (ShortOddC cposYBBY x n k). done. done. done. done.
    + have contra: yel = red. rewrite cpos_x_n_yel. rewrite cpos_x_n_red. done . done. 
  Qed.
  (* End: Three_Color_Triangle_Problem_nec_ShortOdd --------------------*)
  
  (* Begin: Three_Color_Triangle_Problem_nec_LongOdd --------------------*)
  (* colorBYB x n k z : 最上段の x から x+n までの左端＋右端 3^k 個を青，中央を黄で塗る (範囲外は青にする) *)
  Definition colorBYB (x n k z : nat) := if 3^k <= z-x <= n-(3^k) then yel else blu.

  (* colorBYB の性質1 *)
  Lemma lemBYB1: forall x y n k i: nat, (0 <= i <= (3^k).-1) -> blu = colorBYB x n k (x+i). 
  Proof.
    move=> x y n k i range.
    - have T: (colorBYB x n k (x+i) = if 3^k <= i <= n-(3^k) then yel else blu).
      by rewrite- {2 3} (x_plus_y_minus_x_is_y x i). 
    - have H: (3 ^ k <= i <= n - 3 ^ k) = false.
      apply/eqP.
      rewrite eq_false. rewrite eq_dual_and. rewrite ! eq_dual_le.
      apply/orP. left. move: range. move/andP. move=> [A B].
      have H1: (0 < 3^k) = true. by apply expn3Pos.
      by rewrite- eq_adjoint_S_P_le in B. 
    - by rewrite H in T.
  Qed.

  (* colorBYB の性質2 *)
  Lemma lemBYB2: forall x y n k i: nat, (3^k <= i <= n-(3^k)) -> yel = colorBYB x n k (x+i).
  Proof.
    move=> x y n k i range.
    - have T: (colorBYB x n k (x+i) = if 3^k <= i <= n-(3^k) then yel else blu).
      rewrite- {2 3} (x_plus_y_minus_x_is_y x i). done.
    - by rewrite range in T.
  Qed.

  (* colorBYB の性質3 *)
  Lemma lemBYB3: forall x y n k i: nat, ((n-(3^k)).+1 <= i <= n) -> blu = colorBYB x n k (x+i). 
  Proof.
    move=> x y n k i range.
    - have T: (colorBYB x n k (x+i) = if 3^k <= i <= n-(3^k) then yel else blu).
      rewrite- {2 3} (x_plus_y_minus_x_is_y x i). done. 
    - have H: (3 ^ k <= i <= n - 3 ^ k) = false.
      apply/eqP.      
      rewrite eq_false. rewrite eq_dual_and. rewrite ! eq_dual_le.
      apply/orP. right. move: range. move/andP. move=> [A B]. done.
    - by rewrite H in T.
  Qed.

  (* n の範囲条件から導かれる不等式 *)
  Lemma fromRangeN:
    forall k n : nat,
      ((3^k).*2 + 1 <= n < (3^(k.+1))) -> ((3^k) <= n) /\ ((3^k).*2 <= n) /\ (n - (3^k).*2 <= (3^k).-1).
  Proof.
    move => k n. move/andP. move=> [rangeN1 rangeN2]. split. 
    - (* first goal *)
      have X1: ((3^k) <= (3^k).*2 + 1).
      rewrite- addnn. rewrite- addnA. rewrite- eq_le_plus_l. by apply leq0n.
      by apply (trans_lelele X1).
    - (* second goal *)
      have X2: ((3^k).*2 <= n). 
      apply ltnW. rewrite  addn1 in rangeN1. done.
      split. done. 
    - (* third goal *)
      have X3: (0 < 3^k) = true. by apply expn3Pos.
      rewrite- (eq_adjoint_S_P_le (n - (3 ^ k).*2)).
      rewrite eq_adjoint_minus_plus_lt.
      rewrite expnS in rangeN2.
      rewrite (mulnDl 1 2 (3^k)) in rangeN2.
      rewrite mul2n in rangeN2.
      rewrite mul1n in rangeN2. done. done. done. 
  Qed.

  Lemma LongOddA:
    forall cpos:nat->nat->Color,forall x n k : nat,
        ((3^k).*2 + 1 <= n < (3^(k.+1)))
        -> F_mix cpos
        -> (forall(x1 y1:nat), TriangleF cpos x1 y1 (3 ^ k))
        ->(forall i: nat,(0 <= i <= n -> (colorBYB x n k (x+i)) = cpos (x+i) 0))
        -> (
          (forall i: nat,(0 <= i <= n - (3^k).*2 -> red = cpos (x+i) (3^k)))
          /\
          (forall i: nat,(3^k <= i <= n - 3^k -> red = cpos (x+i) (3^k)))
        ).
  Proof.
    - move=> cpos x n k rangeN H_mix triangle topcolor.
      + have A1: (3^k) <= n. by apply fromRangeN. 
      + have A2: (3 ^ k).*2 <= n. by apply fromRangeN.
      + have A3: n - (3^k).*2 <= (3^k).-1. by apply fromRangeN.
      + have exp3Pos: (0 < 3^k) = true. by apply expn3Pos.    
        split.
      + (* first part *)
        move=> i. move /andP. move => [C D].
      + have E: 0 <= i <= n.
        apply /andP. split. done.
        apply (trans_lelele D), leq_subr.
      + have A4: 0 <= i <= (3^k).-1.
        apply/andP. split. done. apply (trans_lelele D A3).
      + have CposB: blu = cpos (x+i) 0. 
        ++ have colB: blu = colorBYB x n k (x+i). apply (lemBYB1 x 0 n k i A4).
        ++ rewrite colB. by apply topcolor.            
      + have CposY: yel = cpos (x+i+(3^k)) 0.
        ++ have A5: 3^k <= (3^k)+i <= n-(3^k).
           apply /andP. split. by rewrite- eq_le_plus_l.
           rewrite- (eq_adjoint_plus_minus_le ((3^k)+i) A1).
           rewrite addnC. rewrite addnA. rewrite addnn.
           rewrite addnC. rewrite eq_adjoint_plus_minus_le. done. done.
        ++ have A6: 0 <= 3 ^ k + i. apply ltnW. move:A5. move/andP. move=>[A5a A5b]. apply (trans_ltlelt exp3Pos). done. 
        ++ have A7: 3 ^ k + i <= n. move:A5. move/andP. move=>[A5a A5b]. apply (trans_lelele A5b). apply leq_subr. 
        ++ have colY: yel = colorBYB x n k (x+(3^k)+i). rewrite- addnA. apply (lemBYB2 x 0 n k ((3^k)+i) A5).
        ++ rewrite colY. rewrite- addnA. rewrite (addnC (3^k) i). rewrite- addnA. apply topcolor. rewrite addnC. done. 
      + have CposR: red = cpos (x+i) (3^k). 
        rewrite- [(3 ^ k)]addn0. rewrite [(3^k + 0)]addnC. specialize (triangle (x+i) 0).
        rewrite/TriangleF in triangle. rewrite- CposB in triangle. apply/ceqP. rewrite- CposY in triangle. done. done.
      + (* second part *)
        move=> i. move /andP. move => [C D].      
      + have E: 0 <= i <= n.
        apply /andP. split. done.
        apply (trans_lelele D), leq_subr.
      + have A4: 3^k <= i <= n-(3^k).
        apply/andP. split. done. done.
      + have CposY: yel = cpos (x+i) 0. 
        ++ have colY: yel = colorBYB x n k (x+i). apply (lemBYB2 x 0 n k i A4). 
        ++ rewrite colY. by apply topcolor. 
      + have CposB: blu = cpos (x+(3^k)+i) 0. 
        ++ have X: n < 3 ^ k.+1. move: rangeN. move/andP. move=>[rangeN1 rangeN2]. done.
        ++ have Y: i <= n - 3 ^ k. done.
        ++ have Z: (3^k) + i <= n. rewrite addnC. rewrite eq_adjoint_plus_minus_le. done. done. 
        ++ have A5: n - 3 ^ k < 3 ^ k + i <= n. 
           apply /andP. split.
           rewrite eq_adjoint_minus_plus_lt. 
           rewrite (addnC (3^k) i). rewrite- addnA. rewrite addnn. 
           apply (trans_lelele X). rewrite expnS.
           rewrite (mulnDl 1 2 (3^k)). rewrite mul2n. rewrite mul1n.
           rewrite- eq_mono_plus_le_plus. done. done. done. 
        ++ have colB: blu = colorBYB x n k (x+(3^k)+i).
           rewrite- addnA. apply (lemBYB3 x 0 n k ((3^k)+i)). done.
        ++ rewrite colB. rewrite- addnA. by apply topcolor.
      + have CposR: red = cpos (x+i) (3^k). 
        rewrite- addnA in CposB. rewrite (addnC (3^k) i)in CposB. rewrite addnA in CposB. 
        rewrite- [(3 ^ k)]addn0. rewrite [(3^k + 0)]addnC. specialize (triangle (x+i) 0).
        rewrite/TriangleF in triangle. rewrite- CposB in triangle. apply/ceqP. rewrite- CposY in triangle. done. done.
  Qed.
  
  Lemma LongOddB:
    forall cpos:nat->nat->Color,forall x n k : nat,
        ((3^k).*2 + 1 <= n < (3^(k.+1)))
        -> F_mix cpos
        -> (forall(x1 y1:nat), TriangleF cpos x1 y1 (3 ^ k))
        -> (forall i: nat,(0 <= i <= n -> (colorBYB x n k (x+i)) = cpos (x+i) 0))
        -> forall i:nat, (0 <= i <= n-(3^k).*2) -> red = cpos (x+i) ((3^k).*2).
  Proof.
    - move=> cpos x n k rangeN H_mix triangle color i rangeI.
      + have A1: (3^k) <= n. by apply fromRangeN. 
      + have A2: (3 ^ k).*2 <= n. by apply fromRangeN.
      + have A3: n - (3^k).*2 <= (3^k).-1. by apply fromRangeN.
      + have A4: i + 3 ^ k <= n - 3 ^ k. rewrite- eq_adjoint_plus_minus_le. rewrite- addnA. rewrite addnn.
        rewrite eq_adjoint_plus_minus_le. done. done. done. 
      + have exp3Pos: (0 < 3^k) = true. by apply expn3Pos.    
      + have [fromA1 fromA2]: 
          (forall i: nat,(0 <= i <= n - (3^k).*2 -> red = cpos (x+i) (3^k)))
          /\ (forall i: nat,(3^k <= i <= n - 3^k -> red = cpos (x+i) (3^k))). by apply LongOddA.
      + have CposR1: red = cpos (x+i) (3^k). 
        apply fromA1. done.
      + have CposR2: red = cpos (x + i + 3 ^ k) (3 ^ k).
        rewrite- addnA. apply fromA2. rewrite leq_addl. rewrite A4. done. 
      + have CposR3: red = cpos (x+i) ((3^k).*2).
        specialize (triangle (x+i) (3^k)). move:triangle. move/ceqP. rewrite/TriangleF. rewrite addnn. 
        rewrite- CposR1. rewrite- CposR2. done. done. 
  Qed.
  
  Lemma LongOddC:
    forall cpos:nat->nat->Color,forall x n k : nat,
        ((3^k).*2 + 1 <= n < (3^(k.+1)))
        -> F_mix cpos
        -> (forall i: nat,(0 <= i <= n -> (colorBYB x n k (x+i)) = cpos (x+i) 0))
        -> (forall(x1 y1:nat), TriangleF cpos x1 y1 (3 ^ k))
        -> red = cpos x n. 
  Proof.
    - move=> cpos x n k rangeN H_mix H_BYB triangle.
      + have rangeN1: (3 ^ k).*2 <= n. by apply fromRangeN.
      + have fromB: forall i:nat, (0 <= i <= n-(3^k).*2 -> red = cpos (x+i) ((3^k).*2)).
        apply LongOddB. done. done. done. done.
      + have fromRR: red = cpos x ((3 ^ k).*2 + (n - (3 ^ k).*2)). 
        apply (AllRed cpos x ((3^k).*2) (n-((3^k).*2))). done. done. 
      + move:fromRR. rewrite addnC. rewrite subnK. done. done. 
  Qed.

  (* 奇数の場合-2 終わり *)
  Lemma Three_Color_Triangle_Problem_nec_LongOdd :
    forall (x n k : nat), ((3^k).*2 + 1 <= n < (3^(k.+1))) -> ~(WellColoredTriangleF x n). 
  Proof.
    - move=> x n k rangeN triangle.
      have [cposBYB [H_mix B]]: exists cposBYB: nat->nat->Color, F_mix cposBYB /\ forall x1 y1: nat, cposBYB x1 y1 = F (colorBYB x n k) x1 y1.
      exists (F (colorBYB x n k)). split. apply cposF. done.
      specialize (triangle cposBYB H_mix).
      have topcolor : forall i : nat, ((0 <= i <= n) -> (colorBYB x n k (x+i)) = cposBYB (x+i) 0).
      move=>i range. rewrite B. done. 
      + move: (rangeN). move/andP. case=>[K1 K2].
      + have A1: (3^k) <= n. by apply fromRangeN.
      + have tri3k: forall x y: nat, TriangleF cposBYB x y (3^k).
        move=> x1 y1. apply Three_Color_Triangle_Problem_suf''.
        exists k. done. done.
      + have cposR: red = cposBYB x n. by apply (LongOddC cposBYB x n k).
      + have cposB1: blu = cposBYB x 0. rewrite- (addn0 x). rewrite- topcolor. rewrite (addn0 x). 
        rewrite- {2} (addn0 x). apply (lemBYB1 x 0). done. done.  
      + have cposB2: blu = cposBYB (x+n) 0. rewrite- topcolor. apply (lemBYB3 x 0). apply/andP. split. 
        rewrite (eq_adjoint_minus_plus_lt n A1). rewrite- eq_lt_plus_l. apply expn3Pos. done. rewrite leqnn. done. 
      + have triBBR: TriangleF cposBYB x 0 n. rewrite/TriangleF. apply/ceqP. rewrite add0n.
        apply/ceqP. done. 
      + have mixRBB: red = mix blu blu. rewrite cposR. rewrite {1} cposB1. rewrite cposB2. apply/ceqP. apply triBBR.
        done. 
  Qed.
  (* End: Three_Color_Triangle_Problem_nec_LongOdd --------------------*)
  
  Theorem Three_Color_Triangle_Problem_nec :
    forall (n x : nat), n > 0 -> (WellColoredTriangleF x n) -> (exists k :nat, n = 3 ^ k).
  Proof.
    move=> n x n_is_not0 Wct.
    case (nat_total n) => k rangeN. case rangeN => [n_is_0|n_is_not0'].
    - by rewrite n_is_0 in n_is_not0.
    - case (odd_or_even n) => [Odd|Even].
      + case n_is_not0' => [n_is_exp3k|n_is_not3k].
        have Isexp3k: exists k:nat,n=3^k. by exists k. by [].
      + case n_is_not3k => [Short|Long].
        * move:(Short). move/andP. case=>[Short1 Short2].
        * exfalso.
          apply (Three_Color_Triangle_Problem_nec_ShortOdd x n k).
          rewrite Short Odd /=. done. done.
        * exfalso.
          apply (Three_Color_Triangle_Problem_nec_LongOdd x n k).
          done. done. 
        * exfalso.
          apply (Three_Color_Triangle_Problem_nec_even x n).
          rewrite n_is_not0 Even /=. done. done.
  Qed.

  Theorem Three_Color_Triangle_Problem_sufnec :
    forall (n x : nat) , n > 0 -> (exists k : nat, n = 3 ^ k) <-> (WellColoredTriangleF x n). 
  Proof.
    move=> n x NotZeroN. split.
    - by apply Three_Color_Triangle_Problem_suf.
    - by apply Three_Color_Triangle_Problem_nec.
  Qed.
  
  (* 終わり *)
  Theorem Three_Color_Triangle_Problem2  :
    forall (n : nat) , n > 0 -> (exists k : nat, n = 3 ^ k) <-> (WellColoredTriangleF 0 n).
  Proof.
    move=>n. by apply Three_Color_Triangle_Problem_sufnec. 
  Qed.
  
(* ------------------------------------------------------------------------------ *)
