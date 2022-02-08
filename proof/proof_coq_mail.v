From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype.

Section nat1.

Let connect3m n m :
  (3 ^ m <= n <= (3 ^ m).*2) || ((3 ^ m).*2.+1 <= n < 3 ^ m.+1)
  <-> 3 ^ m <= n < 3 ^ m.+1.
Proof.
split=> [/orP[/andP[Left1 Left2]|/andP[Right1 Right2]]|/andP[Short1 Short2]].
- rewrite Left1/= (leq_ltn_trans Left2)// expnS -muln2 mulnC.
  by rewrite ltn_mul2r expn_gt0.
- by rewrite Right2 andbT (leq_trans _ Right1)// leqW// -addnn leq_addr.
  have [Less|More] := leqP n (3 ^ m).*2.
  + by rewrite andbT Short1.
  + by rewrite Short2 orbC.
Qed.

Let nat_total' n : exists k,
  n = 0 \/ 3 ^ k <= n <= (3 ^ k).*2 \/ (3 ^ k).*2.+1 <= n < 3 ^ k.+1.
Proof.
elim: n => [| n [k [->|]]]; [by exists 0; left |by exists 0; right; left|].
have [-> _|NotZero /orP] := eqVneq n 0; first by exists 0; right; left.
rewrite connect3m => /andP[rangeN].
rewrite leq_eqVlt => /predU1P[rangeN1|rangeN2].
+ by exists k.+1; right; left; rewrite rangeN1 leqnn -addnn leq_addr.
+ by exists k; right; apply/orP; rewrite connect3m rangeN2 leqW.
Qed.

Lemma nat_total n : exists k,
 n = 0 \/ n = 3 ^ k \/ 3 ^ k < n <= (3 ^ k).*2 \/ (3 ^ k).*2.+1 <= n < 3 ^ k.+1.
Proof.
have [k H] := nat_total' n.
suff K : n = 3 ^ k \/ 3 ^ k < n <= (3 ^ k).*2 <-> 3 ^ k <= n <= (3 ^ k).*2.
  by case : H => [H|[H|H]]; [exists 0; left|exists k; tauto|exists k; tauto].
split=> [[<-|/andP[/ltnW ->//]]|/andP[]].
- by rewrite leqnn -addnn leq_addr.
- by rewrite leq_eqVlt => /predU1P[-> _|-> ->]; [left|right].
Qed.

End nat1.

Section Three_Color_Triangle_definitions.

(* --- 定義一覧 --- *)
Inductive Color : Set := red | yel | blu.
(*三角形三色問題で用いる色の集合 Color を定義 *)
(* 用いる色は次の3色 red:red, yel:yellow, blu:blue のつもり*)

(* ここから Ver6 *)
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

Canonical col_eqMixin := EqMixin eqcolP.
Canonical col_eqType := Eval hnf in EqType Color col_eqMixin.

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
(* 2色を用いて次の段に塗る色を決める演算 mix を定義 *)

(* ----- mix の性質 ----- *)

Lemma mixCut c0 c1 c2 c3 :
  mix (mix (mix c0 c1) (mix c1 c2)) (mix (mix c1 c2) (mix c2 c3)) = mix c0 c3.
Proof. by move: c0 c1 c2 c3 => [] [] [] []. Qed.

Definition coloring := nat -> nat -> Color.

Definition F_mix cpos := forall x y, cpos x y.+1 = mix (cpos x y) (cpos x.+1 y).

(* (x,y) (x+n,y) (x,y+n) の3頂点の色が mix になっている *)
Definition TriangleF cpos x y n :=
  cpos x (y + n) = mix (cpos x y) (cpos (x + n) y).

(* (x,0) から始まる n 段の三角形に要請通りの任意の色塗りをしても 3頂点(x,0),(x+n,0),(x,n)の色は調和している *)
Definition WellColoredTriangleF x n :=
  forall cpos, F_mix cpos -> TriangleF cpos x 0 n.

(* ----- 色づけ関数のリフト (最上段のみ色塗りから全域への色塗りに拡張する) ----- *)
(* ----- 後に定義する colorYBBY や colorBYB などに対して適用する ----- *)
Fixpoint liftpaint (color : nat -> Color) x y :=
  if y is y'.+1 then mix (liftpaint color x y') (liftpaint color x.+1 y')
  else color x.

(* ----- リフトして作った色塗り関数は F_mix を満たす ----- *)
(*Lemma cposF (color : nat -> Color) : F_mix (liftpaint color).
Proof. by []. Qed.*)

End Three_Color_Triangle_definitions.

Section Three_Color_Triangle_Problem.

(* ----- 三角形三色問題 ----- *)
Lemma Three_Color_Triangle_Problem_suf' (cpos : coloring) (k x y : nat) :
  F_mix cpos -> TriangleF cpos x y (3 ^ k).
Proof.
move=> H_mix; elim: k x y => [|k IHk] x y.
- by rewrite expn0 /TriangleF !addn1; exact/H_mix.
- rewrite /TriangleF -(mixCut _ (cpos (x + 3 ^ k) y) (cpos (x + (3 ^ k).*2) y)).
  have <- : TriangleF cpos x y (3 ^ k) by exact: IHk (*Triangle035*).
  rewrite -addnn addnA.
  have <- : TriangleF cpos (x + 3 ^ k) y (3 ^ k) by exact: IHk. (*Triangle346*)
  have <- : TriangleF cpos x (y + 3 ^ k) (3  ^k) by exact: IHk. (*Triangle568*)
  have -> : 3 ^ k.+1 = (3 ^ k).*2 + 3 ^ k.
    by rewrite expnS (mulnDl 1 2) mul1n mul2n addnC.
  rewrite -!addnA addnn !addnA.
  (*Triangle417*)
  have <- : TriangleF cpos (x + (3 ^ k).*2) y (3 ^ k) by exact: IHk.
  rewrite -addnn !addnA.
  (*Triangle679*)
  have <- : TriangleF cpos (x + 3 ^ k) (y + 3 ^ k) (3 ^ k) by exact: IHk.
  rewrite -!addnA addnn !addnA.
  (*Triangle892*)
  have <- : TriangleF cpos x (y + (3 ^ k).*2) (3  ^k) by exact: IHk.
  by rewrite addnAC.
Qed.

(* 十分条件 *)
Theorem Three_Color_Triangle_Problem_suf x n :
  (exists k, n = 3 ^ k) -> WellColoredTriangleF x n.
Proof. by move=> [k ->] cpos; exact: Three_Color_Triangle_Problem_suf'. Qed.

(* ここから必要条件 ------------------------------------*)

Section AllRed.
Variables (cpos : coloring) (x y n : nat).
Hypothesis H_mix : F_mix cpos.
Hypothesis topcolor : forall i, i <= n -> cpos (x + i) y = red.

(* ある段が全て赤ならその下はずっと赤 *)
Let AllRedN q p : p + q <= n -> cpos (x + p) (y + q) = red.
Proof.
elim: q p => [p|q IHq p pqn]; first by rewrite !addn0; apply topcolor.
by rewrite addnS H_mix IHq ?(leq_trans _ pqn)// -?addnS ?IHq// ?addnS// addSnnS.
Qed.

(* ある段が全て赤なら最下段も赤 *)
Lemma AllRed : cpos x (y + n) = red. Proof. by rewrite -(addn0 x) AllRedN. Qed.

End AllRed.

(* Begin: Three_Color_Triangle_Problem_nec_even --------------------*)
(* colorYB x n z : 最上段の x から x+n までのマスを黄，青と交互に塗る (範囲外は黄にする) *) (* 注意：コードが変わった*)
Definition colorYB n x := if (x <= n) && ~~ odd x then yel else blu.

(* colorYB の性質 *)
Lemma lemYB1 n i : i <= n -> ~~ odd i -> colorYB n i = yel.
Proof. by move=> ni oi; rewrite /colorYB ni oi. Qed.

Lemma lemYB2 n i : odd i -> colorYB n i = blu.
Proof. by move=> oi; rewrite /colorYB oi andbF. Qed.

Section Even.
Variables (cpos : coloring) (x n : nat).
Hypotheses (NotZero : n > 0) (H_mix : F_mix cpos).
Hypothesis topcolor : forall i, i <= n -> cpos (x + i) 0 = colorYB n i.

Let EvenA i : i <= n.-1 -> cpos (x + i) 1 = red.
Proof.
move=> rangeI.
(* 最上段のマスが colorYB で塗られていることを示す *)
have rangetop1 : i <= n by rewrite (leq_trans rangeI)// leq_pred.
have Cpos1 := topcolor i rangetop1.
have rangetop2 : i.+1 <= n by rewrite -add1n -leq_subRL ?subn1.
have Cpos2 := topcolor i.+1 rangetop2.
(* 最上段より 1 段下のマスの色は mix と colorYB で得られることを示す *)
have Cpos3 : cpos (x + i) 1 = mix (cpos (x + i) 0) (cpos (x + i).+1 0).
  exact/H_mix.
(* colorYB で塗られている色を求める *)
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

Lemma EvenB : cpos x n = red.
Proof. by rewrite -(prednK NotZero) -add1n AllRed// EvenA. Qed.

End Even.

Lemma Three_Color_Triangle_Problem_nec_even x n :
  n > 0 -> ~~ odd n -> ~ WellColoredTriangleF x n.
Proof.
move=> n_gt0 Even Wct.
have [cposYB[H_mix Paint]] : exists cposYB, F_mix cposYB /\
  forall x1 y1, cposYB x1 y1 = liftpaint (fun y => colorYB n (y - x)) x1 y1.
  by exists (liftpaint (fun y => colorYB n (y - x))).
have := Wct cposYB H_mix.
rewrite /TriangleF addnC addn0.
have <- : colorYB n 0 = cposYB x 0 by rewrite Paint/= subnn.
have <- : colorYB n n = cposYB (x + n) 0 by rewrite Paint/= addnC addnK.
have -> : colorYB n 0 = yel by [].
have -> : colorYB n n = yel by rewrite /colorYB leqnn Even.
have ->// : cposYB x n = red.
by apply: EvenB => // i ni; rewrite Paint/= addnC addnK.
Qed.
(* End: Three_Color_Triangle_Problem_nec_Even --------------------*)

Definition colorYBBY n x :=
  if ((x <= n./2) && odd x) || ((n./2.+1 <= x <= n) && ~~ odd x)
  then blu else yel.

(* colorYBBY の性質 *)
Lemma lemYBBY1 n i : i <= n./2 -> ~~ odd i -> colorYBBY n i = yel.
Proof.
by move=> ni /negbTE oi; rewrite /colorYBBY oi /= !(andbF,andbT)/= ltnNge ni.
Qed.

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

Let ShortOddA i : i <= n - 3 ^ k ->
  colorYB (n - 3 ^ k) i = cpos (x + i) (3 ^ k).
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
have Cpos2 : colorYBBY n (i + 3 ^ k) = cpos (x + i + 3 ^ k) 0.
  by rewrite -addnA color.
have cpos_mix : cpos (x + i) (3 ^ k) =
    mix (cpos (x + i) 0) (cpos (x +i + 3 ^ k) 0).
  by rewrite -triangle.
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

Let C4 : 0 < n - 3 ^ k.
Proof. by rewrite ltn_subCr subn0; move/andP : range => []. Qed.

Let ShortOddB i : i <= (n - 3 ^ k).-1 -> cpos (x + i) (3 ^ k).+1 = red.
Proof.
move=> rangeI.
have rangeI1 : i <= n - 3 ^ k by rewrite (leq_trans rangeI)// leq_pred.
have rangeI2 : i.+1 <= n - 3 ^ k by rewrite (leq_ltn_trans rangeI)// ltn_predL.
(* 3^k 段下のマスの色は colorYB で塗られていることを示す *)
(* 「(x +i,3^k +1) のマスの色は赤」を示すには colorYB の値から mix で計算できる *)
suff : mix (cpos (x  +i) (3 ^ k)) (cpos (x + i).+1 (3 ^ k)) = red by move=> <-.
(* colorYB で塗られている色を示す．i の偶奇で場合分け *)
have [oi|ei] := boolP (odd i).
- rewrite -ShortOddA// (_ : colorYB _ _ = blu); last first.
    by rewrite /colorYB rangeI1 oi.
  by rewrite -addnS -ShortOddA// /colorYB rangeI2/= oi.
- rewrite -(ShortOddA i)// (_ : colorYB _ _ = yel); last first.
    by rewrite /colorYB ei rangeI1.
  by rewrite -addnS -ShortOddA// /colorYB rangeI2 /= ei.
Qed.

Lemma ShortOddC : cpos x n = red.
Proof.
have -> : n = 3 ^ k + 1 + (n - 3 ^ k).-1.
  by rewrite -addnA addnC add1n prednK// ?subnK// ?subn_gt0// ltnW// -subn_gt0.
by rewrite AllRed// => i ?; rewrite addn1 ShortOddB.
Qed.

End ShortOdd.

Lemma Three_Color_Triangle_Problem_nec_ShortOdd x n k :
  3 ^ k < n <= (3 ^ k).*2 -> odd n -> ~ WellColoredTriangleF x n.
Proof.
move=> K oddn; rewrite/WellColoredTriangleF => triangle.
have [cposYBBY [H_mix B]] : exists cposYBBY, F_mix cposYBBY /\
    forall x1 y1, cposYBBY x1 y1 = liftpaint (fun y => colorYBBY n (y - x)) x1 y1.
  by exists (liftpaint (fun y => colorYBBY n (y - x))).
have {}triangle := triangle cposYBBY H_mix.
have A2 i : colorYBBY n i = cposYBBY (x + i) 0 by rewrite B/= addnC addnK.
have cpos_x_n_yel : cposYBBY x n = yel.
  have cpos_x_0_yel : cposYBBY x 0 = yel by rewrite -(addn0 x) -A2 lemYBBY1.
  move: triangle; rewrite /TriangleF.
  have -> : cposYBBY (x + n) 0 = yel.
    have <-// : cposYBBY x 0 = cposYBBY (x + n) 0.
    by rewrite B -A2 -lemYBBY5//= subnn.
  by rewrite cpos_x_0_yel.
have : cposYBBY x n = red.
  by apply: (ShortOddC _ k) => // ? ?; exact: Three_Color_Triangle_Problem_suf'.
by rewrite cpos_x_n_yel.
Qed.
(* End: Three_Color_Triangle_Problem_nec_ShortOdd --------------------*)

(* Begin: Three_Color_Triangle_Problem_nec_LongOdd --------------------*)
(* colorBYB x n k z : 最上段の x から x+n までの左端＋右端 3^k 個を青，中央を黄で塗る (範囲外は青にする) *) (* 注意：コードが変わった*)
Definition colorBYB n k x := if 3 ^ k <= x <= n - 3 ^ k then yel else blu.

(* colorBYB の性質 *)
Lemma lemBYB1 n k i : i <= (3 ^ k).-1 -> colorBYB n k i = blu.
Proof.
move=> range; rewrite /colorBYB ifF//; apply/negbTE.
by rewrite negb_and -ltnNge (leq_ltn_trans range)//= prednK// expn_gt0.
Qed.

Lemma lemBYB2 n k i : 3 ^ k <= i <= n - 3 ^ k -> colorBYB n k i = yel.
Proof. by move=> range; rewrite /colorBYB range. Qed.

Lemma lemBYB3 n k i : (n - 3 ^ k).+1 <= i -> colorBYB n k i = blu.
Proof.
move=> range; rewrite /colorBYB ifF//.
by apply/negbTE; rewrite negb_and orbC -ltnNge range.
Qed.

Section LongOdd.
Variables (cpos : coloring) (k x n : nat).
Hypotheses (rangeN : (3 ^ k).*2.+1 <= n < 3 ^ k.+1) (H_mix : F_mix cpos).
Hypothesis triangle : forall x1 y1, TriangleF cpos x1 y1 (3 ^ k).
Hypothesis color : forall i, i <= n -> colorBYB n k i = cpos (x + i) 0.

(* n の範囲条件から導かれる不等式 *)
Let fromRangeN :
  prod (3 ^ k <= n) (prod ((3 ^ k).*2 <= n) (n - (3 ^ k).*2 <= (3 ^ k).-1)).
Proof.
move: rangeN => /andP[rangeN1 rangeN2]; split.
- by rewrite (leq_trans _ rangeN1)// -addnn -addnS leq_addr.
- rewrite (ltnW rangeN1); split => //.
  rewrite leq_subLR -addnn -ltnS -addnS prednK// ?expn_gt0//.
  move: rangeN2; rewrite expnSr; move/leq_trans; apply.
  by rewrite {2}(_ : 3 = 1 + 1 + 1)// 2!mulnDr !muln1.
Qed.

Let LongOddA :
  (forall i, i <= n - (3 ^ k).*2 -> cpos (x + i) (3 ^ k) = red) /\
  (forall i, 3 ^ k <= i <= n - 3 ^ k -> cpos (x + i) (3 ^ k) = red).
Proof.
split=> [i D|i /andP[C D]]; have E : i <= n by rewrite (leq_trans D)// leq_subr.
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
  rewrite leq_subRL// ?fromRangeN// addnCA addnn addnC -leq_subRL//.
  by rewrite fromRangeN.
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

(* 奇数の場合-2 終わり *)
Lemma Three_Color_Triangle_Problem_nec_LongOdd x n k :
  (3 ^ k).*2.+1 <= n < 3 ^ k.+1 -> ~ WellColoredTriangleF x n.
Proof.
move=> range triangle.
have [cposBYB [H_mix B]] : exists cposBYB, F_mix cposBYB /\
    forall x1 y1, cposBYB x1 y1 = liftpaint (fun y => colorBYB n k (y - x)) x1 y1.
  by exists (liftpaint (fun y => colorBYB n k (y - x))).
have {}triangle := triangle cposBYB H_mix.
have topcolor i : i <= n -> colorBYB n k i = cposBYB (x + i) 0.
  by rewrite B/= addnC addnK.
have tri3k x1 y1 : TriangleF cposBYB x1 y1 (3 ^ k).
  exact: Three_Color_Triangle_Problem_suf'.
have cposR : cposBYB x n = red by exact: (LongOddC _ k).
have cposB1 : cposBYB x 0 = blu by rewrite -(addn0 x) -topcolor// lemBYB1.
have cposB2 : cposBYB (x + n) 0 = blu.
  rewrite -topcolor// lemBYB3// ltn_subrL expn_gt0 /=.
  by move/andP : range => [+ _]; apply: leq_trans.
suff: mix blu blu = red by [].
by rewrite -cposR -{1}cposB1 -cposB2 -[in LHS](add0n n) triangle.
Qed.
(* End: Three_Color_Triangle_Problem_nec_LongOdd --------------------*)

Theorem Three_Color_Triangle_Problem_nec n x :
  n > 0 -> WellColoredTriangleF x n -> exists k, n = 3 ^ k.
Proof.
move=> + Wct; case: (nat_total n) => k [->//|n_is_not0 n_gt0].
have [Odd|Even] := boolP (odd n).
  case: n_is_not0 => [n_is_exp3k|[Short|Long]]; first by exists k.
  - by exfalso; exact: (Three_Color_Triangle_Problem_nec_ShortOdd x n k).
  - by exfalso; exact: (Three_Color_Triangle_Problem_nec_LongOdd x n k).
by exfalso; exact: (Three_Color_Triangle_Problem_nec_even x n).
Qed.

Theorem Three_Color_Triangle_Problem_sufnec n x :
  n > 0 -> (exists k, n = 3 ^ k) <-> WellColoredTriangleF x n.
Proof.
move=> n_gt0; split.
- exact: Three_Color_Triangle_Problem_suf.
- exact: Three_Color_Triangle_Problem_nec.
Qed.

(* 終わり *)
Theorem Three_Color_Triangle_Problem2 n :
  n > 0 -> (exists k, n = 3 ^ k) <-> WellColoredTriangleF 0 n.
Proof. exact: Three_Color_Triangle_Problem_sufnec. Qed.

(* -------------------------------------------------------------------------- *)

End Three_Color_Triangle_Problem.
