From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
(* Three Color Triangle Problem (TCTP) *)

Section Three_Color_Triangle_definitions.

  (* Color: the type for the three colors in TCTP *)
  (* red, blu (=blue), and yel (=yellow) *)
  Inductive Color : Set := red | yel | blu.

  Definition eqcol c0 c1 :=
    match c0, c1 with
    | red, red => true
    | blu, blu => true
    | yel, yel => true
    | _  ,_   => false
    end.

  Lemma eqcolP : Equality.axiom eqcol.
  Proof.
    by move=> n m; apply: (iffP idP) => [|<-]; [move: n m => [| |] [| |]|elim n].
  Qed.

  Canonical Col_eqMixin := EqMixin eqcolP.
  Canonical col_eqType := Eval hnf in EqType Color Col_eqMixin.

  (* The mix operation produces a next color by mixing two given colors *)
  Definition mix c0 c1 :=
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

  Lemma mixCut c0 c1 c2 c3: mix (mix (mix c0 c1) (mix c1 c2)) (mix (mix c1 c2) (mix c2 c3)) = mix c0 c3.
  Proof. by move: c0 c1 c2 c3 => [] [] [] []. Qed.

  Definition coloring := nat -> nat -> Color.

  Definition F_mix cpos := forall x y, cpos x y.+1 = mix (cpos x y) (cpos x.+1 y).

  (* Meaning: The color of the node (x,y+n) is the mixure of those of the nodes (x,y) and (x+n,y). *)
  Definition TriangleF cpos x y n := cpos x (y + n) = mix (cpos x y) (cpos (x + n) y).

  (* Meaning: The triangle (x,0)-(x+n,0)-(x,n) makes a well-colored triangle for any expected coloring. *)
  Definition WellColoredTriangleF x n := forall cpos, F_mix cpos -> TriangleF cpos x 0 n.

  (* Lifting of top-level coloring functions (This will be applied to colorYBBY and colorBYB defined later) *)
  Fixpoint liftpaint (color : nat -> Color) x y :=
    if y is y'.+1 then mix (liftpaint color x y') (liftpaint color x.+1 y') else color x.

End Three_Color_Triangle_definitions.

Section Three_Color_Triangle_Problem.

  Lemma Three_Color_Triangle_Problem_suf (cpos : coloring) (k x y : nat) :
    F_mix cpos -> TriangleF cpos x y (3 ^ k).
  Proof.
    move=> H_mix; elim: k x y => [|k IHk] x y.
    - by rewrite expn0 /TriangleF !addn1; exact/H_mix.
    - rewrite /TriangleF -(mixCut _ (cpos (x + 3 ^ k) y) (cpos (x + (3 ^ k).*2) y)).
      have <- : TriangleF cpos x y (3 ^ k) by exact: IHk.
      rewrite -addnn addnA.
      have <- : TriangleF cpos (x + 3 ^ k) y (3 ^ k) by exact: IHk.
      have <- : TriangleF cpos x (y + 3 ^ k) (3  ^k) by exact: IHk.
      have -> : 3 ^ k.+1 = (3 ^ k).*2 + 3 ^ k.
      by rewrite expnS (mulnDl 1 2) mul1n mul2n addnC.
      rewrite -!addnA addnn !addnA.
      have <- : TriangleF cpos (x + (3 ^ k).*2) y (3 ^ k) by exact: IHk.
      rewrite -addnn !addnA.
      have <- : TriangleF cpos (x + 3 ^ k) (y + 3 ^ k) (3 ^ k) by exact: IHk. 
      rewrite -!addnA addnn !addnA.
      have <- : TriangleF cpos x (y + (3 ^ k).*2) (3  ^k) by exact: IHk.
      by rewrite addnAC.
  Qed.

(* Proof of the necessary condition ------------------------------------*)
Section AllRed.
  (* AllRed: The lower most cell is red if there is a line whose all cells are red *)    
  Variables (cpos : coloring) (x y n : nat).
  Hypothesis H_mix : F_mix cpos.
  Hypothesis topcolor : forall i, i <= n -> cpos (x + i) y = red.

  Lemma AllRed : cpos x (y + n) = red.
  Proof.
    suff AllRed' q p : p + q <= n -> cpos (x + p) (y + q) = red.
    rewrite -(addn0 x); exact: AllRed'.
    elim: q p => [p|q IHq p pqn]; first by rewrite !addn0; apply topcolor.
    by rewrite addnS H_mix IHq ?(leq_trans _ pqn)// -?addnS ?IHq// ?addnS// addSnnS.
  Qed.

End AllRed.

(* Begin: Three_Color_Triangle_Problem_nec_even --------------------*)
(* colorYB x n z : 最上段の x から x+n までのマスを黄，青と交互に塗る (範囲外は黄にする) *)
Definition colorYB n x := if (x <= n) && ~~ odd x then yel else blu.

Section Even.
Variables (cpos : coloring) (x n : nat).
Hypotheses (NotZero : n > 0) (H_mix : F_mix cpos).
Hypothesis topcolor : forall i, i <= n -> cpos (x + i) 0 = colorYB n i.

Lemma Even : cpos x n = red.
Proof.
  suff EvenA i : i <= n.-1 -> cpos (x + i) 1 = red; first by rewrite -(prednK NotZero) -add1n AllRed// EvenA.
  move=> rangeI.
  have rangetop1 : i <= n by rewrite (leq_trans rangeI)// leq_pred.
  have rangetop2 : i.+1 <= n. by rewrite -add1n -leq_subRL ?subn1.
  have Cpos1 := topcolor i rangetop1.
  have Cpos2 := topcolor i.+1 rangetop2.
  have Cpos3 : cpos (x + i) 1 = mix (cpos (x + i) 0) (cpos (x + i).+1 0); first exact/H_mix.
  have lemYB1 m j : j <= m -> ~~ odd j -> colorYB m j = yel by move=> mj oj; rewrite /colorYB mj oj.
  have lemYB2 m j : odd j -> colorYB m j = blu by move=> oj; rewrite /colorYB oj andbF.
  have [OddI|EvenI] := boolP (odd i).
  - have Color1 : colorYB n i = blu by exact: lemYB2.
    have Color2 : colorYB n i.+1 = yel by rewrite lemYB1//= OddI.
    rewrite Color1 in Cpos1; rewrite Color2 in Cpos2.
    by rewrite Cpos1 -addnS Cpos2 /= in Cpos3.
  - have Color1 : colorYB n i = yel by exact: lemYB1.
    have Color2 : colorYB n i.+1 = blu by exact: lemYB2.
    rewrite Color1 in Cpos1; rewrite Color2 in Cpos2.
    by rewrite Cpos1 -addnS Cpos2 /= in Cpos3.
Qed.

End Even.

Lemma Three_Color_Triangle_Problem_nec_even x n : n > 0 -> ~~ odd n -> ~ WellColoredTriangleF x n.
Proof.
  move=> n_gt0 EvenN Wct.
  have [cposYB[H_mix Paint]] : exists cposYB, F_mix cposYB /\ forall x1 y1, cposYB x1 y1 = liftpaint (fun y => colorYB n (y - x)) x1 y1; first by exists (liftpaint (fun y => colorYB n (y - x))).
  have := Wct cposYB H_mix; rewrite /TriangleF addnC addn0.
  have <- : colorYB n 0 = cposYB x 0 by rewrite Paint/= subnn.
  have <- : colorYB n n = cposYB (x + n) 0 by rewrite Paint/= addnC addnK.
  have -> : colorYB n 0 = yel by rewrite /=.
  have -> : colorYB n n = yel by rewrite /colorYB leqnn EvenN.
  have -> // : cposYB x n = red by apply: Even => // i ni; rewrite Paint/= addnC addnK.
Qed.
(* End: Three_Color_Triangle_Problem_nec_Even --------------------*)

Definition colorYBBY n x := if ((x <= n./2) && odd x) || ((n./2.+1 <= x <= n) && ~~ odd x) then blu else yel.

(* Some properties of colorYBBY *)
Lemma lemYBBY1 n i : i <= n./2 -> ~~ odd i -> colorYBBY n i = yel.
Proof. by move=> ni /negbTE oi; rewrite /colorYBBY oi /= !(andbF,andbT)/= ltnNge ni. Qed.

Lemma lemYBBY2 n i : n./2.+1 <= i -> odd i -> colorYBBY n i = yel.
Proof. by move=> r oi; rewrite /colorYBBY oi !(andbF,andbT) leqNgt orbF r. Qed.

Lemma lemYBBY3 n i : i <= n./2 -> odd i -> colorYBBY n i = blu.
Proof. by move=> ni oi; rewrite /colorYBBY ni oi. Qed.

Lemma lemYBBY4 n i : n./2.+1 <= i <= n -> ~~ odd i -> colorYBBY n i = blu.
Proof. by move=> ni /negbTE oi; rewrite /colorYBBY oi !(andbT,andbF) ni. Qed.

Lemma lemYBBY5 n : odd n -> colorYBBY n 0 = colorYBBY n n.
Proof.
  move=> on; rewrite /colorYBBY leq0n on/= !(andbF,andbT) orbF.
  rewrite ifF //; apply/negbTE; rewrite -ltnNge.
  by rewrite -{2}(odd_double_half n) on add1n ltnS -addnn leq_addl.
Qed.

Section ShortOdd.
Variables (cpos : coloring) (k x n : nat).
Hypotheses (range : 3 ^ k < n <= (3 ^ k).*2) (oN : odd n).
Hypothesis H_mix : F_mix cpos.
Hypothesis triangle : forall x1 y1, TriangleF cpos x1 y1 (3 ^ k).
Hypothesis color : forall i, i <= n -> colorYBBY n i = cpos (x + i) 0.

Let ShortOddA i : i <= n - 3 ^ k -> colorYB (n - 3 ^ k) i = cpos (x + i) (3 ^ k).
Proof.
  move=> rangeI.
  have nk2 : n < (3 ^ k).*2.
  move: range => /andP[_]; rewrite leq_eqVlt => /predU1P[nk|//].
  by move: oN; rewrite nk odd_double.
  have ? : n./2 < 3 ^ k.
  rewrite -(@ltn_pmul2l 2)// !mul2n (leq_trans _ nk2)// ltnS.
  by rewrite -{2}(odd_double_half n) oN add1n.
  have ? : n - 3 ^ k <= n./2.
  rewrite leq_subCl -{1}(odd_double_half n) oN add1n -addnn subSn ?leq_addr//.
  by rewrite -addnBA// subnn addn0.
  have ? : i <= n./2 by exact: (leq_trans rangeI).
  have nik : n./2 < i + 3 ^ k by rewrite ltn_addl.
  have ? : i + 3 ^ k <= n.
  by rewrite addnC -leq_subRL// ltnW//; move/andP : range => [].
  have rangeIa : i <= n by rewrite (leq_trans rangeI)// leq_subr.
  have Cpos1 : colorYBBY n i = cpos (x + i) 0 by exact/color/rangeIa.
  have Cpos2 : colorYBBY n (i + 3 ^ k) = cpos (x + i + 3 ^ k) 0 by rewrite -addnA color.
  have cpos_mix : cpos (x + i) (3 ^ k) = mix (cpos (x + i) 0) (cpos (x +i + 3 ^ k) 0); first by rewrite -triangle.
  have lemYB1 m j : j <= m -> ~~ odd j -> colorYB m j = yel by move=> mj oj; rewrite /colorYB mj oj.
  have lemYB2 m j : odd j -> colorYB m j = blu by move=> oj; rewrite /colorYB oj andbF.
  have [oddI|evenI] := boolP (odd i).
  - have blu1 : colorYBBY n i = blu by exact: lemYBBY3.
    have blu2 : colorYBBY n (i + 3 ^ k) = blu.
    by rewrite lemYBBY4// ?nik// oddD oddX orbT oddI.
    have -> : colorYB (n - 3 ^ k) i = blu by exact: lemYB2.
    by rewrite cpos_mix -Cpos1 -Cpos2 blu1 blu2.
  - have YBBYyel1 : colorYBBY n i = yel by exact: lemYBBY1.
    have YBBYyel2 : colorYBBY n (i + 3 ^ k) = yel.
    by rewrite lemYBBY2// ?nik// oddD oddX orbT /= addbT evenI.
    have -> : colorYB (n - 3 ^ k) i = yel by exact: lemYB1.
    by rewrite cpos_mix -Cpos1 -Cpos2 YBBYyel1 YBBYyel2.
Qed.

(* 3^k 段下のマスの色は colorYB で塗られていることを示す *)
  (* 「(x +i,3^k +1) のマスの色は赤」を示すには colorYB の値から mix で計算できる *)
Let ShortOddB i : i <= (n - 3 ^ k).-1 -> cpos (x + i) (3 ^ k).+1 = red.
Proof.
  move=> rangeI.
  have rangeI1 : i <= n - 3 ^ k by rewrite (leq_trans rangeI)// leq_pred.
  have ?: 0 < n - 3 ^ k by rewrite ltn_subCr subn0; move/andP : range => []. 
  have rangeI2 : i.+1 <= n - 3 ^ k by rewrite (leq_ltn_trans rangeI)// ltn_predL.
  suff : mix (cpos (x  +i) (3 ^ k)) (cpos (x + i).+1 (3 ^ k)) = red by move=> <-.
  have [oi|ei] := boolP (odd i).
  - rewrite -ShortOddA// (_ : colorYB _ _ = blu); first by rewrite -addnS -ShortOddA// /colorYB rangeI2/= oi.
    by rewrite /colorYB rangeI1 oi.    
  - rewrite -(ShortOddA i)// (_ : colorYB _ _ = yel); first by rewrite -addnS -ShortOddA// /colorYB rangeI2 /= ei.
    by rewrite /colorYB ei rangeI1.
Qed.

Lemma ShortOddC : cpos x n = red.
Proof.
  have -> : n = 3 ^ k + 1 + (n - 3 ^ k).-1.
  have ?: 0 < n - 3 ^ k by rewrite ltn_subCr subn0; move/andP : range => [].
  by rewrite -addnA addnC add1n prednK// ?subnK// ?subn_gt0// ltnW// -subn_gt0.
  by rewrite AllRed// => i ?; rewrite addn1 ShortOddB.
Qed.

End ShortOdd.

Lemma Three_Color_Triangle_Problem_nec_ShortOdd x n k :
3 ^ k < n <= (3 ^ k).*2 -> odd n -> ~ WellColoredTriangleF x n.
Proof.
  move=> K oddn; rewrite/WellColoredTriangleF => triangle.
  have [cposYBBY [H_mix B]] : exists cposYBBY, F_mix cposYBBY /\ forall x1 y1, cposYBBY x1 y1 = liftpaint (fun y => colorYBBY n (y - x)) x1 y1; first by exists (liftpaint (fun y => colorYBBY n (y - x))).
  have {}triangle := triangle cposYBBY H_mix.
  have A2 i : colorYBBY n i = cposYBBY (x + i) 0 by rewrite B/= addnC addnK.
  have cpos_x_n_yel : cposYBBY x n = yel.
  have cpos_x_0_yel : cposYBBY x 0 = yel by rewrite -(addn0 x) -A2 lemYBBY1.
  move: triangle; rewrite /TriangleF.
  have -> : cposYBBY (x + n) 0 = yel.
  have <- // : cposYBBY x 0 = cposYBBY (x + n) 0; by rewrite B -A2 -lemYBBY5//= subnn.
  by rewrite cpos_x_0_yel.
  have : cposYBBY x n = red.
  apply: (ShortOddC _ k) => // ? ?; exact: Three_Color_Triangle_Problem_suf.
  by rewrite cpos_x_n_yel.
Qed.
(* End: Three_Color_Triangle_Problem_nec_ShortOdd --------------------*)

(* Begin: Three_Color_Triangle_Problem_nec_LongOdd --------------------*)
(* colorBYB x n k z : 最上段の x から x+n までの左端＋右端 3^k 個を青，中央を黄で塗る (範囲外は青にする) *)
Definition colorBYB n k x := if 3 ^ k <= x <= n - 3 ^ k then yel else blu.

(* Some properties of colorBYB *)
Lemma lemBYB1 n k i : i <= (3 ^ k).-1 -> colorBYB n k i = blu.
Proof.
  move=> range; rewrite /colorBYB ifF//; apply/negbTE.
  by rewrite negb_and -ltnNge (leq_ltn_trans range)//= prednK// expn_gt0.
Qed.

Lemma lemBYB2 n k i : 3 ^ k <= i <= n - 3 ^ k -> colorBYB n k i = yel.
Proof. by move=> range; rewrite /colorBYB range. Qed.

Lemma lemBYB3 n k i : (n - 3 ^ k).+1 <= i -> colorBYB n k i = blu.
Proof.
  move=> range; rewrite /colorBYB ifF//; apply/negbTE.
  by rewrite negb_and orbC -ltnNge range.
Qed.

Section LongOdd.
Variables (cpos : coloring) (k x n : nat).
Hypotheses (rangeN : (3 ^ k).*2.+1 <= n < 3 ^ k.+1) (H_mix : F_mix cpos).
Hypothesis triangle : forall x1 y1, TriangleF cpos x1 y1 (3 ^ k).
Hypothesis color : forall i, i <= n -> colorBYB n k i = cpos (x + i) 0.

(* An inequality obtained from the range of n *)
Let fromRangeN : 
  prod (3 ^ k <= n) (prod ((3 ^ k).*2 <= n) (n - (3 ^ k).*2 <= (3 ^ k).-1)).
Proof.
  move: rangeN => /andP[rangeN1 rangeN2]; split.
  - by rewrite (leq_trans _ rangeN1)// -addnn -addnS leq_addr.
  - rewrite (ltnW rangeN1); split => [//|].
    rewrite leq_subLR -addnn -ltnS -addnS prednK// ?expn_gt0//.
    move: rangeN2; rewrite expnSr; move/leq_trans; apply.
    by rewrite {2}(_ : 3 = 1 + 1 + 1)// 2!mulnDr !muln1.
Qed.

Let LongOddA :
  (forall i, i <= n - (3 ^ k).*2 -> cpos (x + i) (3 ^ k) = red) /\
  (forall i, 3 ^ k <= i <= n - 3 ^ k -> cpos (x + i) (3 ^ k) = red).
Proof.
  split=> [i D|i /andP[C D]];
  have E : i <= n by rewrite (leq_trans D)// leq_subr.
  - have CposB : cpos (x + i) 0 = blu.
    rewrite -color//; apply: lemBYB1 => //.
    by rewrite (leq_trans D) // fromRangeN.
    have CposY : cpos (x + i + (3 ^ k)) 0 = yel.
    have A5 : 3 ^ k + i <= n - 3 ^ k.
    by rewrite leq_subRL// ?fromRangeN// addnA addnn -leq_subRL// fromRangeN.
    have A7 : 3 ^ k + i <= n by rewrite (leq_trans A5)// leq_subr.
    have colY : colorBYB n k (3 ^ k + i) = yel by rewrite lemBYB2// leq_addr A5.
    by rewrite -colY -addnA color// (addnC i).
    by have := triangle (x + i) 0; rewrite /TriangleF CposB CposY => ->.
  - have CposY : cpos (x + i) 0 = yel.
    by rewrite -(lemBYB2 n k i)// ?C//; apply/esym/color.
    have : cpos (x + 3 ^ k + i) 0 = blu.
    have ? : n - 3 ^ k < 3 ^ k + i.
    rewrite ltn_subLR// ?(leq_trans C)// addnA addnn.
    case/andP: rangeN => _ /leq_trans ->//.
    by rewrite expnS (mulnDl 1 2) addnC mul2n mul1n leq_add2l.
    have <- : colorBYB n k (3 ^ k +i) = blu by exact: lemBYB3.
    by rewrite -addnA -color// -leq_subRL// fromRangeN.
    rewrite addnAC => CposB; rewrite -[3 ^ k]add0n.
    by have := triangle (x + i) 0; rewrite /TriangleF CposB CposY => ->.
Qed.

Let LongOddB i : i <= n - (3 ^ k).*2 -> cpos (x + i) (3 ^ k).*2 = red.
Proof.
  move=> rangeI.
  have A4 : i + 3 ^ k <= n - 3 ^ k.
  by rewrite leq_subRL// ?fromRangeN// addnCA addnn addnC -leq_subRL// fromRangeN.
  have CposR1 : cpos (x + i) (3 ^ k) = red by exact: LongOddA.1.
  have CposR2 : cpos (x + i + 3 ^ k) (3 ^ k) = red.
  by rewrite -addnA; apply: LongOddA.2; rewrite leq_addl A4.
  by have := triangle (x + i) (3 ^ k); rewrite /TriangleF addnn CposR1 CposR2.
Qed.

Lemma LongOddC : cpos x n = red.
Proof.
  have : cpos x ((3 ^ k).*2 + (n - (3 ^ k).*2)) = red.
  by rewrite AllRed// => i; exact: LongOddB.
  by rewrite addnC subnK// fromRangeN.
Qed.

End LongOdd.
  
Lemma Three_Color_Triangle_Problem_nec_LongOdd x n k :
  (3 ^ k).*2.+1 <= n < 3 ^ k.+1 -> ~ WellColoredTriangleF x n.
Proof.
  move=> range triangle.
  have [cposBYB [H_mix B]] : exists cposBYB, F_mix cposBYB /\ forall x1 y1, cposBYB x1 y1 = liftpaint (fun y => colorBYB n k (y - x)) x1 y1; first by exists (liftpaint (fun y => colorBYB n k (y - x))).
  have {}triangle := triangle cposBYB H_mix.
  have topcolor i : i <= n -> colorBYB n k i = cposBYB (x + i) 0; first by rewrite B/= addnC addnK.
  have tri3k x1 y1 : TriangleF cposBYB x1 y1 (3 ^ k); first exact: Three_Color_Triangle_Problem_suf.
  have cposR : cposBYB x n = red by exact: (LongOddC _ k).
  have cposB1 : cposBYB x 0 = blu by rewrite -(addn0 x) -topcolor// lemBYB1.
  have cposB2 : cposBYB (x + n) 0 = blu.
  rewrite -topcolor// lemBYB3// ltn_subrL expn_gt0 /=.
  by move/andP : range => [+ _]; apply: leq_trans.
  suff: mix blu blu = red by [].
  by rewrite -cposR -{1}cposB1 -cposB2 triangle.
Qed.
       
Lemma nat_total n : exists k, n = 0 \/ n = 3 ^ k \/ 3 ^ k < n <= (3 ^ k).*2 \/ (3 ^ k).*2.+1 <= n < 3 ^ k.+1.
Proof.
  elim: n => [|n [k [IH0|[IH1|[IH2|IH3]]]]]; first by exists 0; left.
  - exists 0; right; left; by rewrite IH0.
  - exists k; right; right; left; by rewrite -IH1 -addnn -addn1 !leq_add2l IH1 expn_gt0.
  - case /andP : IH2 => IH2a ; rewrite leq_eqVlt => /predU1P[->|IH2b].
    case: k IH2a => [|k]; first by exists 1 ; right; left; rewrite expn0 expn1.
    exists (k.+1); right; right; right; apply /andP; split; first by[].
    rewrite (expnSr 3 k.+1) {3}(_:3 = 2+1)// -(addn1 ((3^k.+1).*2)) mulnDr muln2 ltn_add2l muln1.
    by rewrite expnS (ltn_trans (ltnSn 1))// -{1}(muln1 3) leq_pmul2l//expn_gt0.
    by exists k; right; right; left; apply/andP; split; [exact:ltnW|].
  - case /andP : IH3 => IH3a; rewrite leq_eqVlt => /predU1P[|IH3b]; first by exists (k.+1); right; left.
    by exists k; right; right; right; apply/andP; split; [rewrite (ltn_trans IH3a)|].
Qed. 
 
Theorem Three_Color_Triangle_Problem_nec n x :
  n > 0 -> WellColoredTriangleF x n -> exists k, n = 3 ^ k.
Proof.
  move=> + Wct; case: (nat_total n) => k [->//|n_is_not0 n_gt0]. 
  have [Odd|Even] := boolP (odd n).
  case: n_is_not0 => [n_is_exp3k|[Short|Long]]; first by exists k.
  - by exfalso; exact: (Three_Color_Triangle_Problem_nec_ShortOdd x n k).
  - by exfalso; exact: (Three_Color_Triangle_Problem_nec_LongOdd x n k).
  - by exfalso; exact: (Three_Color_Triangle_Problem_nec_even x n).
Qed.

Theorem Three_Color_Triangle_Problem_sufnec n x :
  n > 0 -> (exists k, n = 3 ^ k) <-> WellColoredTriangleF x n.
Proof.
  move=> n_gt0; split => [[k] n_is_exp3k cpos|]; first rewrite n_is_exp3k.
  - exact: (Three_Color_Triangle_Problem_suf cpos k x 0).
  - exact: Three_Color_Triangle_Problem_nec.
Qed.

(* Main Theorem *)
Theorem Three_Color_Triangle_Problem n :
  n > 0 -> (exists k, n = 3 ^ k) <-> WellColoredTriangleF 0 n.
Proof. exact: Three_Color_Triangle_Problem_sufnec. Qed.

End Three_Color_Triangle_Problem.





(* Lemma nat_total n : exists k, *)
(*     n = 0 \/ n = 3 ^ k \/ 3 ^ k < n <= (3 ^ k).*2 \/ (3 ^ k).*2.+1 <= n < 3 ^ k.+1. *)
(* Proof. *)
(*   have H(k): 3^k>=1 by [apply (leq_ltn_trans (leq0n k)); apply ltn_expl]. *)
(*   elim n. exists 0. by left. *)
(*   move=> n0 [k0 [IH0|[IH1|[IH2|IH3]]]]. *)
(*   exists 0. by rewrite IH0; right; left. *)
(*   exists k0. by rewrite -IH1; right;right;left; rewrite -addnn -addn1 !leq_add2l IH1; apply H. *)
(*   case/andP : IH2 => IH2a; rewrite leq_eqVlt => /predU1P[->|B]. case: k0 IH2a=>[K0|k0]. *)
(*   exists 1; right;left. by rewrite expn0 expn1. *)
(*   exists (k0.+1); right;right;right. *)
(*   have H1: 3^k0.+1>1 by rewrite expnS (ltn_trans (ltnSn 1))// -{1}(muln1 3) leq_pmul2l// apply H. *)
(*   apply /andP; split=>//. *)
(*   by rewrite (expnSr 3 k0.+1) {3}(_:3 = 2+1)// -(addn1 ((3^k0.+1).*2)) mulnDr muln2 ltn_add2l muln1. *)
(*   exists k0; right;right;left; apply/andP; split. by apply ltnW. by [].  *)
(*   case/andP: IH3=>IH3. rewrite leq_eqVlt => /predU1P[A|B]. exists (k0.+1). by right;left.  *)
(*   exists k0; right;right;right. apply/andP; split; last first. by []. by rewrite (ltn_trans IH3). *)
(* Qed.  *)
