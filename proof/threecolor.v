From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype.

(* Three Color Triangle Problem (TCTP) *)
Section TCTP_definitions.
  (* Color: the type for the three colors in TCTP *)
  (* red, blu (=blue), and yel (=yellow) *)
  Inductive Color : Set := red | yel | blu.

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

  Lemma mixcut c0 c1 c2 c3: mix (mix (mix c0 c1) (mix c1 c2)) (mix (mix c1 c2) (mix c2 c3)) = mix c0 c3.
  Proof. by move: c0 c1 c2 c3 => [] [] [] []. Qed.

  Definition coloring := nat -> nat -> Color.
  Definition CFun colfun := forall x y, colfun x y.+1 = mix (colfun x y) (colfun x.+1 y).

  (* Meaning: The color of the node (x,y+n) is the mixure of those of the nodes (x,y) and (x+n,y). *)
  Definition Triangle colfun x y n := colfun x (y + n) = mix (colfun x y) (colfun (x + n) y).

  (* Meaning: The triangle (x,0)-(x+n,0)-(x,n) makes a well-colored triangle for any expected coloring. *)
  Definition WellColoredTriangle x n := forall colfun, CFun colfun -> Triangle colfun x 0 n.

  (* Lifting of top-level coloring functions (This will be applied to colorYBBY and colorBYB defined later) *)
  Fixpoint liftcoloring (topcoloring : nat -> Color) x y :=
    if y is y'.+1 then mix (liftcoloring topcoloring x y') (liftcoloring topcoloring x.+1 y') else topcoloring x.
End TCTP_definitions.

Section TCTP.
(* Proof of the sufficient conditions ------------------------------------*)
  Theorem TCTP_suf (colfun : coloring) (k x y : nat) : CFun colfun -> Triangle colfun x y (3 ^ k).
  Proof.
    move=> H.
    elim: k x y => [|k IHk] x y; first by rewrite expn0 /Triangle !addn1; exact /H.
    rewrite /Triangle -(mixcut _ (colfun (x + 3 ^ k) y) (colfun (x + (3 ^ k).*2) y)).
    have <- : Triangle colfun x y (3 ^ k) by exact: IHk.
    rewrite -addnn addnA.
    have <- : Triangle colfun (x + 3 ^ k) y (3 ^ k) by exact: IHk.
    have <- : Triangle colfun x (y + 3 ^ k) (3  ^k) by exact: IHk.
    have -> : 3 ^ k.+1 = (3 ^ k).*2 + 3 ^ k by rewrite expnS (mulnDl 1 2) mul1n mul2n addnC.
    rewrite -!addnA addnn !addnA.
    have <- : Triangle colfun (x + (3 ^ k).*2) y (3 ^ k) by exact: IHk.
    rewrite -addnn !addnA.
    have <- : Triangle colfun (x + 3 ^ k) (y + 3 ^ k) (3 ^ k) by exact: IHk. 
    rewrite -!addnA addnn !addnA.
    have <- : Triangle colfun x (y + (3 ^ k).*2) (3  ^k) by exact: IHk.
    by rewrite addnAC.
  Qed.

(* Proof of the necessary condition ------------------------------------*)
Section allred.
  (* allred: The lower most cell is red if there is a line whose all cells are red *)    
  Variables (colfun : coloring) (x y n : nat).
  Hypothesis H : CFun colfun.
  Hypothesis redline : forall i, i <= n -> colfun (x + i) y = red.

  Lemma allred : colfun x (y + n) = red.
  Proof.
    suff bottom q p : p + q <= n -> colfun (x + p) (y + q) = red by rewrite -(addn0 x); exact: bottom. 
    elim: q p => [p|q IHq p pqn]; first by rewrite !addn0; apply redline.
    by rewrite addnS H IHq ?(leq_trans _ pqn)// -?addnS ?IHq// ?addnS// addSnnS.
  Qed.
End allred.

(* Begin: TCTP_nec_even --------------------*)
(* coloringYB x n: 最上段の x から x+n までのマスを黄，青と交互に塗る (範囲外は黄にする) *)
Definition coloringYB n x := if (x <= n) && ~~ odd x then yel else blu.

Section TCTP_nec_even.
Variables (colfun : coloring) (x n : nat).
Hypotheses (n_gt_0 : n > 0) (H : CFun colfun).
Hypothesis topcolor : forall i, i <= n -> colfun (x + i) 0 = coloringYB n i.

Lemma even_bottom : colfun x n = red.
Proof.
  suff even_next_red i : i <= n.-1 -> colfun (x + i) 1 = red; first by rewrite -(prednK n_gt_0) -add1n allred//.
  move=> i_leq_pn.
  have i_leq_n : i <= n by rewrite (leq_trans i_leq_pn) // leq_pred.
  have i_lt_n : i < n by rewrite -add1n -leq_subRL ?subn1.
  have -> : colfun (x + i) 1 = mix (colfun (x + i) 0) (colfun (x + i).+1 0); first exact/H.
  have -> := topcolor i i_leq_n; rewrite -addnS.
  have -> := topcolor i.+1 i_lt_n.
  have YB_yel m j : j <= m -> ~~ odd j  -> coloringYB m j = yel.
  by move=> m_gt_j oj; rewrite /coloringYB m_gt_j oj.
  have YB_blu m j : odd j -> coloringYB m j = blu by move=> oj; rewrite /coloringYB oj andbF.
  have [oi|ei] := boolP (odd i).
  - have -> : coloringYB n i = blu by exact: YB_blu.
    have -> // : coloringYB n i.+1 = yel by rewrite YB_yel //= oi.
  - have -> : coloringYB n i = yel by exact: YB_yel.
    have -> // : coloringYB n i.+1 = blu by exact: YB_blu.
Qed.
End TCTP_nec_even.

Lemma TCTP_nec_even x n : n > 0 -> ~~ odd n -> ~ WellColoredTriangle x n.
Proof.
  move=> n_gt_0 en WCT.
  have H: CFun (liftcoloring (fun y => coloringYB n (y - x))). by auto.
  have := WCT _ H; rewrite /Triangle addnC addn0.
  have <- : coloringYB n 0 = liftcoloring (fun y => coloringYB n (y - x)) x 0. by rewrite/= subnn.
  have <- : coloringYB n n = liftcoloring (fun y => coloringYB n (y - x)) (x + n) 0 by rewrite/= addnC addnK.
  have -> : coloringYB n 0 = yel by rewrite /=.
  have -> : coloringYB n n = yel by rewrite /coloringYB leqnn en.
  have -> // : liftcoloring (fun y => coloringYB n (y - x)) x n = red by apply: even_bottom => // i ni; rewrite /= addnC addnK.
Qed.
  
(* End: TCTP_nec_even --------------------*)

(* Begin: TCTP_nec_shortodd --------------------*)
Definition coloringYBBY n x := if ((x <= n./2) && odd x) || ((n./2.+1 <= x <= n) && ~~ odd x) then blu else yel.

(* Some properties of coloringYBBY *)
Lemma YBBY_yel_even n i : i <= n./2 -> ~~ odd i -> coloringYBBY n i = yel.
Proof. by move=> i_leq_hn /negbTE oi; rewrite /coloringYBBY oi /= !(andbF,andbT)/= ltnNge i_leq_hn. Qed.

Lemma YBBY_yel_odd n i : n./2.+1 <= i -> odd i -> coloringYBBY n i = yel.
Proof. by move=> r oi; rewrite /coloringYBBY oi !(andbF,andbT) leqNgt orbF r. Qed.

Lemma YBBY_blu_odd n i : i <= n./2 -> odd i -> coloringYBBY n i = blu.
Proof. by move=> ni oi; rewrite /coloringYBBY ni oi. Qed.

Lemma YBBY_blu_even n i : n./2.+1 <= i <= n -> ~~ odd i -> coloringYBBY n i = blu.
Proof. by move=> ni /negbTE oi; rewrite /coloringYBBY oi !(andbT,andbF) ni. Qed.

Lemma YBBY_both n : odd n -> coloringYBBY n 0 = coloringYBBY n n.
Proof.
  move=> on; rewrite /coloringYBBY leq0n on/= !(andbF,andbT) orbF.
  rewrite ifF //; apply/negbTE; rewrite -ltnNge.
  by rewrite -{2}(odd_double_half n) on add1n ltnS -addnn leq_addl.
Qed.

Section TCTP_nec_shortodd.
Variables (colfun : coloring) (k x n : nat).
Hypotheses (n_range : 3 ^ k < n <= (3 ^ k).*2) (on : odd n).
Hypothesis H : CFun colfun.
Hypothesis triangle : forall x1 y1, Triangle colfun x1 y1 (3 ^ k).
Hypothesis topcolor : forall i, i <= n -> coloringYBBY n i = colfun (x + i) 0.

(* 3^k 段下のマスの色は colorYB で塗られていることを示す *)
Let shortodd_coloringYB i : i <= n - 3 ^ k -> coloringYB (n - 3 ^ k) i = colfun (x + i) (3 ^ k).
Proof.
  move=> i_range.
  have i_range' : i + 3 ^ k <= n.
  by rewrite addnC -leq_subRL// ltnW//; move/andP : n_range => [].
  have i_leq_n : i <= n by rewrite (leq_trans i_range)// leq_subr.
  have n_range_lt : n < (3 ^ k).*2.
  move: n_range => /andP[_]; rewrite leq_eqVlt => /predU1P[n_range_eq|//].
  by move: on; rewrite n_range_eq odd_double.
  have hn_range_lt : n./2 < 3 ^ k.
  rewrite -(@ltn_pmul2l 2)// !mul2n (leq_trans _ n_range_lt)// ltnS.
  by rewrite -{2}(odd_double_half n) on add1n.
  have hn_range_lt' : n./2 < i + 3 ^ k by rewrite ltn_addl //.
  have hn_geq_i : i <= n./2. apply: (leq_trans i_range).
  by rewrite leq_subCl -{1}(odd_double_half n) on add1n -addnn subSn ?leq_addr// -addnBA// subnn addn0.
  have -> : colfun (x + i) (3 ^ k) = mix (colfun (x + i) 0) (colfun (x +i + 3 ^ k) 0) by rewrite -triangle.
  have <- : coloringYBBY n i = colfun (x + i) 0 by exact /topcolor /i_leq_n.
  have <- : coloringYBBY n (i + 3 ^ k) = colfun (x + i + 3 ^ k) 0 by rewrite -addnA topcolor.
  have [oi|ei] := boolP (odd i).
  - have -> : coloringYBBY n i = blu by exact: YBBY_blu_odd.
    have -> : coloringYBBY n (i + 3 ^ k) = blu.
    by rewrite YBBY_blu_even// ?hn_range_lt'// oddD oddX orbT oi.
    have ->// : coloringYB (n - 3 ^ k) i = blu by rewrite /coloringYB oi i_range //.
  - have -> : coloringYBBY n i = yel by exact: YBBY_yel_even.      
    have -> : coloringYBBY n (i + 3 ^ k) = yel.
    by rewrite YBBY_yel_odd// ?hn_range_lt'// oddD oddX orbT /= addbT ei.
    have ->// : coloringYB (n - 3 ^ k) i = yel by rewrite /coloringYB ei i_range //.
Qed.

Lemma shortodd_bottom : colfun x n = red.
Proof.
  have shortodd_coloringYB_next_red i : i <= (n - 3 ^ k).-1 -> colfun (x + i) (3 ^ k).+1 = red.
  have n_gt_0: 0 < n - 3 ^ k by rewrite ltn_subCr subn0; move /andP : n_range => [].
  move=> i_range.
  have i_range_leq : i <= n - 3 ^ k by rewrite (leq_trans i_range)// leq_pred.
  have i_range_lt : i.+1 <= n - 3 ^ k by rewrite (leq_ltn_trans i_range)// ltn_predL.
  suff : mix (colfun (x + i) (3 ^ k)) (colfun (x + i).+1 (3 ^ k)) = red by move=> <-.
  have [oi|ei] := boolP (odd i).
  - rewrite -shortodd_coloringYB// (_ : coloringYB _ _ = blu).
    by rewrite -addnS -shortodd_coloringYB// /coloringYB i_range_lt /= oi.
    by rewrite /coloringYB i_range_leq oi.    
  - rewrite -(shortodd_coloringYB i)// (_ : coloringYB _ _ = yel).
    by rewrite -addnS -shortodd_coloringYB// /coloringYB i_range_lt /= ei.
    by rewrite /coloringYB ei i_range_leq.
  have -> : n = 3 ^ k + 1 + (n - 3 ^ k).-1.
  have n_gt_0 : 0 < n - 3 ^ k by rewrite ltn_subCr subn0; case /andP : n_range. 
  by rewrite -addnA addnC add1n prednK// ?subnK// ?subn_gt0// ltnW// -subn_gt0.
  by rewrite allred// => i ?; rewrite addn1 shortodd_coloringYB_next_red.
Qed.
End TCTP_nec_shortodd.

Lemma TCTP_nec_shortodd x n k : 3 ^ k < n <= (3 ^ k).*2 -> odd n -> ~ WellColoredTriangle x n.
Proof.
  move=> n_range on WCT.
  have [colfun [H lift]] : exists colfun, CFun colfun /\ forall x1 y1, colfun x1 y1 = liftcoloring (fun y => coloringYBBY n (y - x)) x1 y1.
  by exists (liftcoloring (fun y => coloringYBBY n (y - x))).
  have := WCT colfun H; rewrite /Triangle addnC addn0.
  have topcolor i : coloringYBBY n i = colfun (x + i) 0 by rewrite lift/= addnC addnK.
  have <- : colfun x 0 = colfun (x + n) 0; first by rewrite lift -topcolor -YBBY_both//= subnn.
  have -> : colfun x 0 = yel by rewrite lift/= subnn.
  have -> // : colfun x n = red by apply: (shortodd_bottom _ k) => // ? ?; apply: TCTP_suf.
Qed.
(* End: TCTP_nec_shortodd --------------------*)

(* Begin: TCTP_nec_longodd --------------------*)
(* colorBYB x n k z : 最上段の x から x+n までの左端＋右端 3^k 個を青，中央を黄で塗る (範囲外は青にする) *)
Definition coloringBYB n k x := if 3 ^ k <= x <= n - 3 ^ k then yel else blu.

(* Some properties of colorBYB *)
Lemma BYB_blu_left n k i : i <= (3 ^ k).-1 -> coloringBYB n k i = blu.
Proof.
  move=> range; rewrite /coloringBYB ifF//; apply/negbTE.
  by rewrite negb_and -ltnNge (leq_ltn_trans range)//= prednK// expn_gt0.
Qed.

Lemma BYB_yel_center n k i : 3 ^ k <= i <= n - 3 ^ k -> coloringBYB n k i = yel.
Proof. by move=> range; rewrite /coloringBYB range. Qed.

Lemma BYB_blu_right n k i : (n - 3 ^ k).+1 <= i -> coloringBYB n k i = blu.
Proof. by move=> range; rewrite /coloringBYB ifF//; apply/negbTE;rewrite negb_and orbC -ltnNge range. Qed.

Section TCTP_nec_longodd.
Variables (colfun : coloring) (k x n : nat).
Hypotheses (n_range : (3 ^ k).*2.+1 <= n < 3 ^ k.+1) (H : CFun colfun).
Hypothesis triangle : forall x1 y1, Triangle colfun x1 y1 (3 ^ k).
Hypothesis topcolor : forall i, i <= n -> coloringBYB n k i = colfun (x + i) 0.

(* An inequality obtained from the range of n *)
Let inequality : prod (3 ^ k <= n) (prod ((3 ^ k).*2 <= n) (n - (3 ^ k).*2 <= (3 ^ k).-1)).
Proof.
  move: n_range => /andP[n_range_left n_range_right]; split.
  - by rewrite (leq_trans _ n_range_left)// -addnn -addnS leq_addr.
  - rewrite (ltnW n_range_left); split => [//|].
    rewrite leq_subLR -addnn -ltnS -addnS prednK// ?expn_gt0//.
    move: n_range_right; rewrite expnSr; move/leq_trans; apply.
    by rewrite {2}(_ : 3 = 1 + 1 + 1)// 2!mulnDr !muln1.
Qed.

Let longodd_red_both_sides :
  (forall i, i <= n - (3 ^ k).*2 -> colfun (x + i) (3 ^ k) = red) /\
  (forall i, 3 ^ k <= i <= n - 3 ^ k -> colfun (x + i) (3 ^ k) = red).
Proof.
  split=> [i i_range_right|i /andP[i_range_left i_range_right]];
  have i_leq_n : i <= n by rewrite (leq_trans i_range_right)// leq_subr.
  - have i_range_right' : 3 ^ k + i <= n - 3 ^ k.
    by rewrite leq_subRL// ?inequality// addnA addnn -leq_subRL// inequality.
    have n_range_geq : 3 ^ k + i <= n by rewrite (leq_trans i_range_right')// leq_subr.
    have -> := triangle (x + i) 0; rewrite /Triangle.
    have -> : colfun (x + i) 0 = blu.
    rewrite -topcolor//; apply: BYB_blu_left => //.
    by rewrite (leq_trans i_range_right) // inequality.
    have ->// : colfun (x + i + (3 ^ k)) 0 = yel.
    by rewrite -addnA -topcolor// (addnC i) // BYB_yel_center// leq_addr i_range_right'//.
  - have ni_range : n - 3 ^ k < 3 ^ k + i.
    rewrite ltn_subLR// ?(leq_trans i_range_left)// addnA addnn.
    case /andP: n_range => _ /leq_trans ->//.
    by rewrite expnS (mulnDl 1 2) addnC mul2n mul1n leq_add2l.
    have -> := triangle (x + i) 0; rewrite /Triangle.
    have -> : colfun (x + i) 0 = yel
    by rewrite -topcolor // ?(BYB_yel_center n k i)// i_range_left i_range_right.
    have ->// : colfun (x + i + 3 ^ k) 0 = blu.
    rewrite addnAC -addnA -topcolor//; first by apply BYB_blu_right.
    by rewrite -leq_subRL// inequality //.
Qed.

Lemma longodd_bottom : colfun x n = red.
Proof.
  have longodd_redline i : i <= n - (3 ^ k).*2 -> colfun (x + i) (3 ^ k).*2 = red.
  move=> i_range; rewrite -addnn.
  have in_range : i + 3 ^ k <= n - 3 ^ k.
  by rewrite leq_subRL// ?inequality// addnCA addnn addnC -leq_subRL// inequality.
  have ->// := triangle (x + i) (3 ^ k); rewrite /Triangle. 
  have ->// : colfun (x + i) (3 ^ k) = red by exact: longodd_red_both_sides.1.
  have ->// : colfun (x + i + 3 ^ k) (3 ^ k) = red.
  by rewrite -addnA; apply: longodd_red_both_sides.2; rewrite leq_addl.    
  have // : colfun x ((3 ^ k).*2 + (n - (3 ^ k).*2)) = red by rewrite allred//.
  by rewrite addnC subnK// inequality.
Qed.
End TCTP_nec_longodd.
  
Lemma TCTP_nec_longodd x n k :
  (3 ^ k).*2.+1 <= n < 3 ^ k.+1 -> ~ WellColoredTriangle x n.
Proof.
  move=> n_range WCT.
  have [colfun [H lift]] : exists colfun, CFun colfun /\ forall x1 y1, colfun x1 y1 = liftcoloring (fun y => coloringBYB n k (y - x)) x1 y1.
  by exists (liftcoloring (fun y => coloringBYB n k (y - x))).
  have := WCT colfun H; rewrite /Triangle addnC addn0.
  have topcolor i : i <= n -> coloringBYB n k i = colfun (x + i) 0; first by rewrite lift /= addnC addnK. rewrite /WellColoredTriangle in WCT.
  have triangle x1 y1 : Triangle colfun x1 y1 (3 ^ k); first exact: TCTP_suf.
  have -> : colfun x n = red; first by exact: (longodd_bottom _ k).
  have -> : colfun x 0 = blu by rewrite -(addn0 x) -topcolor// BYB_blu_left.
  have ->// : colfun (x + n) 0 = blu.
  rewrite -topcolor// BYB_blu_right// -ltn_subCl// ?subnn ?expn_gt0//.
  by move /andP : n_range => [+ _]; apply: leq_trans; rewrite leqW// -addnn leq_addl. 
Qed.
(* End: TCTP_nec_longodd --------------------*)
       
Lemma nat_case n : exists k, n = 0 \/ n = 3 ^ k \/ 3 ^ k < n <= (3 ^ k).*2 \/ (3 ^ k).*2.+1 <= n < 3 ^ k.+1.
Proof.
  elim: n => [|n [k [IH0|[IH1|[|]]]]]; first by exists 0; left.
  - exists 0; right; left; by rewrite IH0.
  - exists k; right; right; left; by rewrite -IH1 -addnn -addn1 !leq_add2l IH1 expn_gt0.
  - case /andP => IH2L; rewrite leq_eqVlt => /predU1P[->|IH2R].
    case: k IH2L => [|k]; first by exists 1 ; right; left; rewrite expn0 expn1.
    exists (k.+1); right; right; right; apply /andP; split; first by[].
    rewrite (expnSr 3 k.+1) {3}(_:3 = 2+1)// -(addn1 ((3^k.+1).*2)) mulnDr muln2 ltn_add2l muln1.
    by rewrite expnS (ltn_trans (ltnSn 1))// -{1}(muln1 3) leq_pmul2l//expn_gt0.
    by exists k; right; right; left; apply/andP; split; [exact:ltnW|].
  - case /andP => IH3L; rewrite leq_eqVlt => /predU1P[|IH3R]; first by exists (k.+1); right; left.
    by exists k; right; right; right; apply/andP; split; [rewrite (ltn_trans IH3L)|].
Qed. 
 
Theorem TCTP_nec n x :
  n > 0 -> WellColoredTriangle x n -> exists k, n = 3 ^ k.
Proof.
  move=> + WCT; case: (nat_case n) => k [->//|n_case n_gt0]. 
  have [on|en] := boolP (odd n).
  - case: n_case => [n_is_exp3k|[shortodd|longodd]]; first by exists k.
    + by exfalso; exact: (TCTP_nec_shortodd x n k).
    + by exfalso; exact: (TCTP_nec_longodd x n k).
  - by exfalso; exact: (TCTP_nec_even x n).
Qed.

Theorem TCTP_sufnec n x :
  n > 0 -> (exists k, n = 3 ^ k) <-> WellColoredTriangle x n.
Proof.
  move=> n_gt0; split => [[k] n_is_exp3k colfun|]; first rewrite n_is_exp3k.
  - exact: (TCTP_suf colfun k x 0).
  - exact: TCTP_nec.
Qed.

(* Main Theorem *)
Theorem TCTP n :
  n > 0 -> (exists k, n = 3 ^ k) <-> WellColoredTriangle 0 n.
Proof. exact: TCTP_sufnec. Qed.
End TCTP.
