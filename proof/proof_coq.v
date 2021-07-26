Require Import PeanoNat Le Lt Plus Mult Even.
From mathcomp
     Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import Classical_Prop.
Require Import Psatz.
Require Import CoqNat MyRewrite.

Notation "x .^ y" :=  (expn x y)%coq_nat (at level 30, right associativity).

Section nat1.

  (* --- _.+1 _.+2 _+3 の性質 --- *)  
  Lemma addn1' : forall n :nat, n.+1 = n + 1.
  Proof.
    move=> n.
    by rewrite addn1.
  Qed.

  Lemma addn10 : forall n : nat, n.+1 = 1 -> n = 0.
  Proof.
    elim=> [ | n IHn].
    - by [].
    - by [].
  Qed.

  (* --- 加法の性質 --- *)

  Lemma add11 : 1 + 1 = 2.
  Proof. by rewrite /=. Qed.

  Lemma add3 : 3 = 2 + 1.
  Proof. by rewrite /=. Qed.
  
  Lemma addpm : forall m n p : nat, m = n -> p + m = p + n.
  Proof.
    move=> m n p eq.
    by rewrite eq.
  Qed.

  Lemma addmp : forall m n p : nat, m = n -> m + p = n + p.
  Proof.
    move=> m n p eq.
    by rewrite eq.
  Qed.

Lemma x_plus_y_minus_x_is_y: forall x y : nat, x+y-x = y.
Proof.
  move=> x y.
  have G1: x + y = y + x. apply Nat.add_comm.
  rewrite G1. rewrite- addnBA.
  have G2: (x-x)%coq_nat = 0.
  apply Nat.sub_diag. rewrite- coqnat_minus in G2. rewrite G2.
  apply Nat.add_0_r. apply coqnat_le, le_n.
Qed.

  (* --- 減法の性質 --- *)
  Lemma x_minus_x_is_0 : forall x : nat, x - x = 0.
  Proof.
    elim=> [ | x IHx].
    done. by rewrite subSS.
  Qed.

  (* --- 乗法の性質 --- *)

  Lemma addnnmul2n : forall n : nat, n + n = 2 * n.
  Proof.
    elim=> [ | n IHn].
    - by [].
    - rewrite<- addn1; rewrite addnA.
      rewrite [(n+1)+n]addnC.
      rewrite [n+(n+1)]addnA.
      rewrite IHn.
      rewrite<- addnA.
      by rewrite add11 mulnDr.
  Qed.

  Lemma mulnDr' :
    forall m n p : nat, (m + n) * p = m * p + n * p.
  Proof.
    move=> m n.
    elim=> [ | p IHp].
    - by rewrite 3!muln0.
    - rewrite mulnC.
      rewrite [m * p.+1]mulnC; rewrite [n*p.+1]mulnC.
      by apply mulnDr.
  Qed.
  
  (* --- 指数の性質 --- *)

  Lemma mul1n' : forall n : nat, n = 1 * n.
  Proof.
    move=> n.
    by rewrite mul1n.
  Qed.
    
  Lemma add3n3n :
    forall n : nat, (3 .^ n) + (3 .^ n) = 2 * (3 .^ n).
  Proof.
    case=> [ | n].
    - by rewrite expn0.
    - by rewrite addnnmul2n.
  Qed.

  Lemma mul33n : forall n : nat, 3 * 3 .^ n = 3 .^ (n + 1).
  Proof.
    elim=> [ | n IHn].
    - by [].
    - rewrite expnS IHn.
      rewrite<- expnS.
      by rewrite 2!addn1.
  Qed.
  
  Lemma add23n3n :
    forall n : nat, 2 * (3 .^ n) + (3 .^ n) = 3 .^ (n.+1).
  Proof.
    move=> n.
    rewrite {2}[3.^n]mul1n'.
    rewrite<- mulnDr'.
    rewrite mul33n.
    rewrite addnS.
    by rewrite addn0.
  Qed.

  Lemma succ3n :
    forall n : nat, 3 .^ (n.+1) = 3 .^ (n + 1).
  Proof.
    move=> n.
    rewrite addnS.
    by rewrite addn0.
  Qed.

  Lemma expn0' : forall n : nat,  n .^ 0 <= 1.
  Proof.
    move=> n.
    by rewrite expn0.
  Qed.

  Lemma expnPos: forall n m : nat, 0 < n -> 0 < n .^ m.
  Proof.
    move=> n m.
    rewrite expn_gt0.
    move=> pos_n.
    apply/orP.
    by left.
  Qed.

  Lemma expn3neq0 : forall m, 3.^m != 0.
  Proof.
    move=> m. rewrite- lt0n. by apply expnPos.  
  Qed.

  Lemma expn3Pos : forall m, 0 < 3.^m .
  Proof.
    move=> m. by apply expnPos. 
  Qed.
  
  Lemma expn2n0' : forall n : nat, 0 < 2 * n .^ 0.
  Proof.
    move=> n.
    rewrite expn0.
    by rewrite muln1.
  Qed.

  Lemma case0 : forall n : nat, n = 0 \/ n > 0.
  Proof.
    elim=> [ | n IHn].
    - left. done.
    - right; by apply ltn0Sn.
  Qed.

  Lemma case01 : forall n : nat, n = 0 \/ n = 1 \/ n > 1.
  Proof.
    elim=> [ | n IHn].
    - by left.
    - case IHn => H0.
      + rewrite H0.
        right; left.
        by [].
      + case H0 => H1.
        rewrite H1.
        right; right.
        by [].
        right; right.
        apply /ltP; apply le_S; by apply /ltP.
  Qed.

  Lemma case1 : forall n : nat, n.+1 = 1 \/ n.+1 > 1.
  Proof.
    elim=> [ | n IHn].
    - by left.
    - case IHn => H0.
      + rewrite H0.
        by right.
      + right.
        apply /ltP; apply le_S; by apply /ltP.
  Qed.

  Lemma case3m1 :
    forall (n m : nat), (n.+1 <= 3 .^ m.+1) -> ((n.+1 < 3 .^ (m.+1)) \/ (n.+1 = 3 .^ m.+1)).
  Proof.
    move=> n m.
    rewrite 2!coqnat_lt.
    by apply le_lt_or_eq.
  Qed.

  Lemma leq23m_3m1 :
    forall (n m : nat), (n <= 2 * 3 .^ m) -> (n < 3 .^ m.+1).
  Proof.
    move=> n m H.
    have two_M_le_three_M : 2 * 3 .^ m < 3 * 3 .^ m.
    apply/coqnat_lt.
    apply/Mult.mult_lt_compat_r.
    apply/coqnat_lt.
    by [].
    apply/coqnat_lt.
    apply/expnPos.
    by []. 
    apply/coqnat_lt.
    apply (PeanoNat.Nat.le_lt_trans n (2 * 3 .^ m) (3 .^ m.+1)).
    apply/coqnat_le.
    by [].
    apply/coqnat_lt.
    rewrite expnS.
    rewrite {2}add3.
    rewrite mulnDr'.
    apply/coqnat_lt.
    apply PeanoNat.Nat.add_lt_mono_r.
    have tmp: (1 * 3.^ m = 3 .^ m).
    apply/PeanoNat.Nat.mul_1_l.
    rewrite-{1} tmp.
    apply Mult.mult_lt_compat_r.
    by [].
    apply/coqnat_lt.
    apply expnPos.
    by [].    
  Qed.
  
  Lemma leq3m_23m1 :
    forall (n m : nat), (2 * 3 .^ m + 1 <= n) -> (3 .^ m <= n).
  Proof.
    move=> n m.
    suff : (3 .^ m <= 2 * 3 .^ m + 1).
    move=> tmp1 tmp2.
    apply coqnat_le.
    apply (PeanoNat.Nat.le_trans (3 .^ m) (2 * 3 .^ m + 1) n).
    by apply coqnat_le.
    by apply coqnat_le. 
    rewrite mul2n.
    rewrite- addnn.
    apply coqnat_le.
    rewrite (_ : 3 .^ m + 3 .^ m + 1 = (3 .^ m + (3 .^ m + 1))%coq_nat).
    apply PeanoNat.Nat.le_add_r.    
    by rewrite- plus_assoc_reverse.            
  Qed.

  Lemma leqNatOr:
    forall (n m : nat), (n <= m) \/ (m + 1 <= n).
  Proof.
    move=> n m.
    have le_sum_gt: {(n <= m)%coq_nat} + {(m.+1 <= n)%coq_nat}.
    apply Compare_dec.le_le_S_dec.
    case le_sum_gt => [le|gt].
    - left.
      by apply coqnat_le.
    - right.
      rewrite (_: (m+1)= (m.+1)).
      by apply coqnat_le.
    by apply addn1.
  Qed.
  
  Lemma leq23m_23m1 :
    forall (n m : nat), (n <= 2 * 3 .^ m) \/ (2 * 3 .^ m + 1 <= n).
  Proof.
    move=> n m.
    apply leqNatOr.
  Qed.

  Lemma connect :
    forall n m : nat, (3 .^ m <= n /\ n <= 2 * 3 .^ m) \/ (2 * 3 .^ m + 1 <= n /\ n < 3 .^ m.+1) <-> (3 .^ m <= n /\ n < 3 .^ m.+1).
  Proof.
    move=> n m.
    split.
    - move=> H.
      case H => [Left|Right].
      + destruct Left as [Left1 Left2].
        split.
        * by [].
        * by apply leq23m_3m1.
      + destruct Right as [Right1 Right2].
        split.
        * by apply leq3m_23m1.
        * by [].
    - move=> H.
      destruct H as [Left Right].
      case (leq23m_23m1 n m).
      + move=> H.
        left.
        split.
        * by [].
          by [].
      + move=> H.
        right.
        split.
        * by [].
          by [].
  Qed.

  Lemma leq3m_3m1 :
    forall (n : nat), 3 .^ n < 3 .^ n.+1.
  Proof.
    move=> n.
    rewrite expnS.
    rewrite {1} (mul1n' (3.^n)).
    apply coqnat_lt.
    apply Mult.mult_lt_compat_r.
    apply coqnat_lt.
    by [].
    apply coqnat_lt.
    by apply expnPos.       
  Qed.

  Lemma oddexpn: forall n m : nat, odd m -> odd (m.^n).
  Proof.
    move=> n. 
    elim n. done. move=> k ind m. 
    rewrite expnS. rewrite oddM. move=>odd. apply/andP. split. done.
    by rewrite ind. 
  Qed.

  Lemma odd3m: forall m : nat, odd (3.^m).
  Proof.
    move=> m. by apply oddexpn. 
  Qed.

  
  Lemma leqn_n1 :
    forall (n m : nat), 3 .^ m <= n -> 3 .^ m <= n.+1.
  Proof.
    move=> n m H.
    suff H1: n < n.+1.
    have P : (3.^m < n.+1)%coq_nat.
    apply (PeanoNat.Nat.le_lt_trans (3 .^ m) n (n.+1)).
    by apply coqnat_le.
    by apply coqnat_le.
    apply coqnat_le; by apply PeanoNat.Nat.lt_le_incl.
    by []. 
  Qed.

  Lemma leq_false1 : forall n i : nat, n./2.+1 <= i <= n -> (0 <= i <= n./2 = false).
  Proof.
    move=> n i.
    move /andP. move=> [] range1 range2. rewrite /=.
    apply ltn_geF. done.
  Qed.

  Lemma leq_false2 : forall n i : nat, 0 <= i <= n./2 -> (n./2.+1 <= i <= n = false).
  Proof.
    move=> n i.
    move /andP. move=> [] range1 range2.
    apply /andP. apply /andP. rewrite negb_and.
    apply /orP. left. rewrite- leqNgt. done.
  Qed.

  Lemma leq_half1 : forall n : nat, n./2 <= n.
  Proof.
    move=> n.
    rewrite- {2} (odd_double_half n).
    rewrite- addnn.
    rewrite- eq_assoc_plus.
    rewrite- eq_adjoint_minus_plus_le. 
    by rewrite x_minus_x_is_0.
  Qed.

  (*  odd n は n <> 0 でもよいが今後の証明がしやすいように odd n とする *)
  Lemma leq_half2 : forall n : nat, odd n -> (n./2).+1 <= n.
  Proof.
    move=>n H.
    rewrite- {2} (odd_double_half n).
    rewrite- addnn.
    rewrite- eq_assoc_plus.
    rewrite- eq_S_le_add_r.
    rewrite H. by [].
  Qed.

  Lemma OddS : forall n : nat, odd n.+1 = ~~ odd n.
  Proof. done. Qed.

  Lemma odd_or_even : forall n : nat, odd n \/ odd n = false.
  Proof.
    elim=> [ | n IHn].
    - right. done.
    - case IHn => [Odd|Even].
      + right. by rewrite OddS Odd.
      + left. by rewrite OddS Even.
  Qed.
  
End nat1.


Section Classical.

  Definition LEM : Prop := forall P : Prop, P \/ ~P.
  Definition DNE : Prop := forall P : Prop, ~(~P) -> P.
  
  Lemma LEMiffDNE : LEM <-> DNE.
  Proof.
    rewrite /LEM /DNE.
    split.
    - move=> LEM P.
      have: P \/ ~P.
      by apply LEM.
      rewrite /not.
      by case.
    - move=> DNE P.
      apply DNE.
      move=> nLEM.
      apply nLEM.
      right.
      move=> PisTrue.
      apply nLEM.
      by left.
  Qed.
  
  (* Axiom classic : forall P : Prop, P \/ ~P. *)
  (* Lemma NNPP : forall P : Prop, ~(~P) -> P. *)
  (* Axiom classic と LEM，Lemma NNPP とDNE はそれぞれ同じ言明 *)

  (* Lemma imply_to_or : forall P Q : Prop, (P -> Q) -> ~ P \/ Q. *)
  
  Lemma Contraposition : forall P Q : Prop, (P -> Q) <-> (~Q -> ~P).
  Proof.
    split.
    - move=> PtoQ nQ QisTrue.
      apply nQ.
      by apply PtoQ.
    - move=> nQtonP PisTrue.
      apply imply_to_or in nQtonP.
      case nQtonP.
      + by apply NNPP.
      + by [].
  Qed.
  
End Classical.

Section Three_Color_Triangle_Problem_suf.

  Inductive Color : Set :=
  | red
  | yel
  | blu.
  (*三角形三色問題で用いる色の集合 Color を定義 *)
  (* 用いる色は次の3色 red:red, yel:yellow, blu:blue のつもり*) 

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

  Parameter Cpos : nat -> nat -> Color -> Prop.
  (* 逆三角形の左から x:nat 番目，上から y:nat 番目の色が c:Color である *)

  Parameter Cconf : Color -> Color -> Color -> Prop.
  (* c0  c1 c2 : Color が3色互いに 同じ色 または 異なる色 である *)

  (* ----- 公理一覧 ----- *)
  Axiom C_exists : forall x y : nat, (exists c : Color, Cpos x y c).
  (* すべてのマスに色が塗られている *)

  Axiom C_uniq :
    forall x y : nat, forall c0 c1 : Color, (Cpos x y c0 /\ Cpos x y c1) -> c0 = c1.
  (* 1つのマスに塗れる色は1色までである *)

  Axiom C_mix :
    forall x y : nat, forall c0 c1 c2 : Color, (Cpos x y c0 /\ Cpos (x + 1) y c1 /\ Cpos x (y + 1) c2) -> c2 = mix c0 c1. 
  (* 隣接する2つのマスの色に演算 mix を適用すると下のマスの色が決まる *)

  Axiom C_paint : forall x y i : nat, forall f:nat -> Color, Cpos (x+i) y (f (x+i)).
  (* 最上行のどの場所も好きな色を塗ることができる *)

  (* Axiom C_conf : *)
  (*   forall x y : nat, forall c0 c1 c2 : Color, Cconf c0 c1 c2 <-> (c0 = c1 /\ c1 = c2 /\ c2 = c0) \/ (c0 <> c1 /\ c1 <> c2 /\ c2 <> c0). *)
  (* c0 c1 c2 : Color が3色互いに 同じ色 または 異なる色 である *)
  (* これは公理ではなく，Cconf の定義 (CHECK) *)


  
  Definition Triangle x y n c0 c1 c2 := Cpos x y c0 /\ Cpos (x+n) y c1 /\ Cpos x (y+n) c2 -> c2 = mix c0 c1.
  (* ----- mix, Cconf の性質 ----- *)
  Lemma mixCom (c0 c1 : Color) : mix c0 c1 = mix c1 c0.
  Proof. case c0, c1; by rewrite /=. Qed.
  
  Lemma mixCut (c0 c1 c2 c3 : Color) :
    mix ( mix (mix c0 c1) (mix c1 c2) ) ( mix (mix c1 c2) (mix c2 c3) ) = mix c0 c3.
  Proof. case c0, c1, c2, c3; by rewrite /=. Qed.

  Lemma falseColor (x y : nat) (c0 c1 : Color) :
    c0 <> c1 /\ Cpos x y c0 /\ Cpos x y c1 -> False.
  Proof.
    move=> H; destruct H as [Differ C0_C1].
    (*have B : blu = mix red yel. by rewrite/=.*)
    case c0, c1.
    - by case Differ.
    - have Uniq : (Cpos x y red /\ Cpos x y yel) -> red = yel.
      apply C_uniq. by specialize (Uniq C0_C1).
    - have Uniq : (Cpos x y red /\ Cpos x y blu) -> red = blu.
      apply C_uniq. by specialize (Uniq C0_C1).
    - have Uniq : (Cpos x y yel /\ Cpos x y red) -> yel = red.
      apply C_uniq. by specialize (Uniq C0_C1).
    - by case Differ.
    - have Uniq : (Cpos x y yel /\ Cpos x y blu) -> yel = blu.
      apply C_uniq. by specialize (Uniq C0_C1).
    - have Uniq : (Cpos x y blu /\ Cpos x y red) -> blu = red.
      apply C_uniq. by specialize (Uniq C0_C1).
    - have Uniq : (Cpos x y blu /\ Cpos x y yel) -> blu = yel.
      apply C_uniq. by specialize (Uniq C0_C1).      
    - by case Differ.
  Qed.

  (* 一辺 n+1 の三角形が triangle則 を満たしているなら最下頂点の色は mix で計算できる *)
  Lemma Bottom_color_of_triangle:
    forall(x y n :nat) (c0 c1 : Color), 
        (forall c0 c1 c2: Color, Triangle x y n c0 c1 c2)
        -> Cpos x y c0
        -> Cpos (x+n) y c1
        -> Cpos x (y+n) (mix c0 c1).
  Proof.
    move=> x y n c0 c1 triangle Cpos0 Cpos1. 
    have [c CposX]: exists c: Color, Cpos x (y+n) c. by apply C_exists.
    have CposAnd: (Cpos x y c0) /\ (Cpos (x+n) y c1) /\ (Cpos x (y+n) c). done. 
    have c_is_mix: c = mix c0 c1. by apply triangle.
    by rewrite- c_is_mix. 
  Qed.
  
    
    
  
  (* ----- 三角形三色問題 ----- *)
                                                                                                              
  Lemma Three_Color_Triangle_Problem_suf' :
    forall (k n x y : nat) (c0 c1 c2 : Color), n = 3 .^ k -> Triangle x y n c0 c1 c2.
  Proof.
    elim=> [ | k IHk ].
    - move=> n x y c0 c1 c2 Step.
      rewrite expn0 in Step. rewrite Step.
      rewrite /Triangle. by apply C_mix.
    - move=> n x y c0 c1 c2 Step.
      move=> [] Cpos0. move=> [] Cpos1 Cpos2.
      
      (* マスに塗られている色に名前をつける *)
      + have: exists c : Color, Cpos (x+3.^k) y c.
        by apply C_exists. case; move=> c3 Cpos3.
      + have: exists c : Color, Cpos (x+((3.^k).*2)) y c.
        by apply (C_exists ((x+(3.^k).*2)) y). case; move=> c4 Cpos4.
      + have: exists c : Color, Cpos x (y+3.^ k) c.
        by apply (C_exists x (y+3.^k)). case; move=> c5 Cpos5.
      + have: exists c : Color, Cpos (x+3.^k) (y+3.^k) c.
        by apply (C_exists (x+3.^k) (y+3.^k)). case; move=> c6 Cpos6.
      + have: exists c : Color, Cpos (x+(3.^k).*2) (y+3.^k) c.
        by apply (C_exists (x+(3.^k).*2) (y+3.^k)). case; move=> c7 Cpos7.
      + have: exists c : Color, Cpos x (y+(3.^k).*2) c.
        by apply (C_exists x (y + (3.^k).*2)). case; move=> c8 Cpos8.
      + have: exists c : Color, Cpos (x+3.^k) (y + (3.^k).*2) c.
         by apply (C_exists (x+3.^k) (y + (3.^k).*2)). case; move=> c9 Cpos9.
          

      (* 6 個の 3 .^ k 段の逆三角形 *)
      + have Triangle035 : Triangle x y (3.^k) c0 c3 c5.
        by apply IHk.
      + have Triangle346 : Triangle (x+3.^k) y (3.^k) c3 c4 c6.
        by apply IHk.
      + have Triangle417 : Triangle (x+(3.^k).*2) y (3.^k) c4 c1 c7.
        by apply IHk.
      + have Triangle568 : Triangle x (y+3.^k) (3.^k) c5 c6 c8.
        by apply IHk.
      + have Triangle679 : Triangle (x+3.^k) (y+3.^k) (3.^k) c6 c7 c9.
        by apply IHk.
      + have Triangle892 : Triangle x (y+(3.^k).*2) (3.^k) c8 c9 c2.
        by apply IHk.
        
    (* それぞれの逆三角形における Cpos の関係から mix の関係を導く *)
      + have mix035 : c5 = mix c0 c3.
        apply Triangle035. done.
      + have mix346 : c6 = mix c3 c4.
        apply Triangle346.
        * apply conj. done.
        * apply conj. rewrite- addnA; rewrite add3n3n mul2n. done.
        * done.
      + have mix417 : c7 = mix c4 c1.
        apply Triangle417.
        * apply conj. done.
        * apply conj. rewrite- mul2n.
           rewrite- addnA. rewrite add23n3n. rewrite- Step. done.
        * done.
      + have mix568 : c8 = mix c5 c6.
        apply Triangle568.
        * apply conj. done.
        * apply conj. done.
        * rewrite- addnA; rewrite add3n3n mul2n. done.
      + have mix679 : c9 = mix c6 c7.
        apply Triangle679.
        * apply conj. done.
        * apply conj. rewrite- addnA; rewrite add3n3n mul2n. done.
        * rewrite- addnA; rewrite add3n3n mul2n. done.
      + have mix892 : c2 = mix c8 c9.
        apply Triangle892.
        * apply conj. done.
        * apply conj. done.
        * rewrite- addnA. rewrite- mul2n. rewrite add23n3n. rewrite- Step.
          done.

      (* mixCut を用いて証明を完了させる *)
      rewrite mix568 mix679 in mix892.
      rewrite mix035 mix346 mix417 in mix892.
      rewrite mix892.
      by apply mixCut.
  Qed.

  Theorem Three_Color_Triangle_Problem_suf :
    forall (x y n : nat),
      ((exists k : nat, n = 3 .^ k) -> forall (c0 c1 c2 : Color),(Triangle x y n c0 c1 c2)).
  Proof.
    move=> x y n.
    case; move=> k Step c0 c1 c2.
    by apply (Three_Color_Triangle_Problem_suf' k n x y).
  Qed.
  
End Three_Color_Triangle_Problem_suf.



Section Three_Color_Triangle_Problem_nec.

  (* Lemma caseN : *)
  (*   forall n : nat, (exists k : nat, ( n = 0 \/ (3 .^ k <= n /\ n <= 2 * 3 .^ k) \/ (2 * 3 .^ k + 1 <= n /\ n < 3 .^ k.+1))). *)
  (* Proof. *)
  (*   elim=> [ | n IHn]. *)
  (*   - exists 0. *)
  (*     by left.  *)
  (*   - destruct IHn as [m]. *)
  (*     move: H => IHm. *)
  (*     case IHm => IHm'. *)
  (*     exists 0; rewrite IHm'. *)
  (*     right; left. *)
  (*     by split.  *)
      
  (*     have Case1 : n.+1 = 1 \/ n.+1 >= 2. *)
  (*     by apply (case1 n).   *)

  (*     case Case1 => Case1'. *)
  (*     + exists 0. *)
  (*       right; left. *)
  (*       rewrite Case1'. *)
  (*       by rewrite /=. *)

  (*     + have Case3m1 : (n.+1 < 3 .^ m.+1) \/ (n.+1 = 3 .^ (m.+1)). *)
  (*       apply case3m1. *)
  (*       case IHm' => Range. *)
  (*       destruct Range as [Range1 Range2]. *)
  (*       by apply leq23m_3m1. *)
  (*       by destruct Range as [Range1 Range2]. *)

  (*       case Case3m1 => Case3m1'. *)
  (*       * exists m. *)
  (*         move: IHm'; rewrite connect; move=> IHm'. *)
  (*         rewrite connect. *)
  (*         destruct IHm' as [IHm'_left IHm'_right]. *)
  (*         right. *)
  (*         split. *)
  (*         by apply leqn_n1. *)
  (*         by [].  *)
  (*       * exists (m.+1). *)
  (*         move: IHm'; rewrite connect; move=> IHm'. *)
  (*         rewrite connect. *)
  (*         destruct IHm' as [IHm'_left IHm'_right]. *)
  (*         right. *)
  (*         rewrite Case3m1'. *)
  (*         split. *)
  (*         by []. *)
  (*         by apply leq3m_3m1. *)
  (* Qed. *)

  Lemma rangeN : forall n : nat, exists k : nat, (n = 0) \/ (3.^k <= n <= (3.^k).*2) \/ ((3.^k).*2 + 1 <= n < (3.^(k.+1))).
  Proof.
    elim=> [ | n IHn].
    - exists 0. left. done.
    - move: IHn. case. move=> k IHn.
      case IHn.
      + move=> Zero.
        rewrite Zero. exists 0. rewrite /=. right; left. done.

      (* 不等式を書き換えるための補題 *)  
      + have Short1 : 3 .^ k <= n <= (3 .^ k).*2 <-> (3 .^ k <= n /\ n <= 2 * (3 .^ k)).
        apply conj.
        move=> H. apply /andP. by rewrite mul2n.
        move=> H. apply /andP. by rewrite mul2n in H.
        
      + have Long1 : (3 .^ k).*2 + 1 <= n < 3 .^ k.+1 <-> 2 * (3 .^ k) + 1 <= n /\ n < 3 .^ k.+1.
        apply conj.
        move=> H. apply /andP. by rewrite mul2n.
        move=> H. apply /andP. by rewrite mul2n in H.
      + have Short2 : 3 .^ k <= n.+1 <= (3 .^ k).*2 <-> (3 .^ k <= n.+1 /\ n.+1 <= 2 * (3 .^ k)).
        apply conj.
        move=> H. apply /andP. by rewrite mul2n.
        move=> H. apply /andP. by rewrite mul2n in H.
        
      + have Long2 : (3 .^ k).*2 + 1 <= n.+1 < 3 .^ k.+1 <-> 2 * (3 .^ k) + 1 <= n.+1 /\ n.+1 < 3 .^ k.+1.
        apply conj.
        move=> H. apply /andP. by rewrite mul2n.
        move=> H. apply /andP. by rewrite mul2n in H.

      + have Boundary : (n.+1 = 3 .^ k.+1) <-> (n.+1 == 3 .^ k.+1).
        apply conj => H. by apply /eqP. by apply /eqP.

      (* 証明再開 *)
      (* n.+1 = 1 と n.+1 > 1 で場合分け *)
      + case (case1 n) => [Zero|NotZero].      
        (* n.+1 = 1 のとき *)
        * rewrite Zero. exists 0. right; left. by rewrite /=.
        (* n.+1 > 1 のとき *)
        * rewrite Short1 Long1 connect. move /andP. move => rangeN.          
          (* n.+1 = 3 .^ k と n.+1 < 3 .^ k.+1で場合分け *)
          have rangeBoundary : (n.+1 = 3 .^ k.+1) \/ (n.+1 < 3 .^ k.+1).
          move: rangeN. move /andP; move=> [] ranegeN1 rangeN2.
          rewrite Boundary. apply /orP. by rewrite leq_eqVlt in rangeN2.
          case rangeBoundary => [rangeN1|rangeN2].
          (* n.+1 = 3 .^ k のとき *)
          ** exists (k.+1). rewrite rangeN1. right; left.
             apply /andP. apply conj. done.
             rewrite- addnn. rewrite- eql_minus_le_le_plus_l.
             rewrite x_minus_x_is_0. done.
          ** exists k. rewrite Short2 Long2 connect. right. apply conj.
             move: rangeN. move /andP. move=> [] range1 range2.
             apply leqW. done. done.
  Qed.        
               
  (* Lemma caseN' : *)
  (*   forall (n : nat), ( even n \/ ( odd n /\ exists k : nat, (3 .^ k <= n <= 2 * 3 .^ k) \/ (2 * 3 .^ k + 1 <= n < 3 .^ k.+1))). *)  

  (* Lemma Paint_Alternate : *)
  (*   forall y : nat, *)
  (*     ((forall (x1 : nat), (exists k1, x1 = 2 * k1) -> Cpos x1 y blu) /\ (forall (x2 : nat), (exists k2, x2 = 2 * k2 + 1) -> Cpos x2 y yel)) -> *)
  (*     (forall (x : nat), Cpos x (y + 1) red). *)
  (* Proof. *)
  (*   move=> y Paint x; destruct Paint as [Paint_Even Paint_Odd]. *)
  (*   case (even_or_odd x). *)
  (*   + rewrite  even_equiv. *)
  (*     rewrite /Nat.Even. *)
  (*     move=> H; destruct H as [m]. *)
  (*     * have Blue : Cpos x y blu. *)
  (*       apply Paint_Even. *)
  (*       by exists m.      *)
  (*     * have Yellow : Cpos (x + 1) y yel. *)
  (*       apply Paint_Odd. *)
  (*       exists m. *)
  (*       by apply addmp. *)
  (*     * have Red : exists c : Color, Cpos x (y + 1) c. *)
  (*       by apply C_exists. *)
  (*       destruct Red as [c]. *)
  (*     * have Mix : c = mix blu yel. *)
  (*       apply (C_mix x y). *)
  (*       by split. *)
  (*       rewrite /= in Mix; by rewrite Mix in H0. *)
  (*   + rewrite  odd_equiv. *)
  (*     rewrite /Nat.Odd. *)
  (*     move=> H; destruct H as [m]. *)
  (*     * have Yellow : Cpos x y yel. *)
  (*       apply Paint_Odd. *)
  (*       by exists m.      *)
  (*     * have Blue : Cpos (x + 1) y blu. *)
  (*       apply Paint_Even. *)
  (*       exists (m + 1). *)
  (*       rewrite mulnDr. *)
  (*       rewrite muln1. *)
  (*       rewrite H. *)
  (*     * have elim_plus : ((2 * m)%coq_nat + 1)%coq_nat = (2 * m)%coq_nat + 1. *)
  (*       by []. *)
  (*       rewrite elim_plus. rewrite- addnA add11. *)
  (*       by []. *)
  (*     * have Red : exists c : Color, Cpos x (y + 1) c. *)
  (*       by apply C_exists. *)
  (*       destruct Red as [c].   *)
  (*     * have Mix : c = mix yel blu. *)
  (*       apply (C_mix x y). *)
  (*       by split. *)
  (*       rewrite /= in Mix; by rewrite Mix in H0. *)
  (* Qed. *)

  (* Lemma Red_Y1 : *)
  (*   forall (y : nat), *)
  (*     (forall (x1 :nat), Cpos x1 y red) -> (forall (x2 :nat), Cpos x2 (y + 1) red). *)
  (* Proof. *)
  (*   move=> y Paint x2. *)
  (*   - have Red1 : Cpos x2 y red. *)
  (*     by apply Paint. *)
  (*   - have Red2 : Cpos (x2 + 1) y red. *)
  (*     by apply Paint. *)
  (*   - have Red' : exists c : Color, Cpos x2 (y + 1) c. *)
  (*     by apply C_exists. *)
  (*     destruct Red' as [c' C'].  *)
  (*   - have Mix : c' = mix red red. *)
  (*     apply (C_mix x2 y). *)
  (*     by split. *)
  (*   - rewrite /= in Mix; by rewrite Mix in C'. *)
  (* Qed. *)
  
  (* Lemma Red_N : *)
  (*   forall (n y : nat), *)
  (*     (forall (x1 :nat), Cpos x1 y red) -> (forall (x2 :nat), Cpos x2 (y + n) red). *)
  (* Proof. *)
  (*   elim=> [ | n IHn]. *)
  (*   - move=> y Paint x2; rewrite addn0. *)
  (*     by apply Paint. *)
  (*   - move=> y Paint x2; rewrite- addn1. *)
  (*     rewrite addnA. *)
  (*     apply Red_Y1; move=> x1. *)
  (*     apply IHn. *)
  (*     move=> x0. *)
  (*     + have Red1 : Cpos x0 y red. *)
  (*       by apply Paint. *)
  (*     + have Red2 : Cpos (x0 + 1) y red. *)
  (*       by apply Paint. *)
  (*     + have Red' : exists c : Color, Cpos x0 (y + 1) c. *)
  (*       by apply C_exists. *)
  (*       destruct Red' as [c' C'].  *)
  (*     + have Mix : c' = mix red red. *)
  (*       apply (C_mix x0 y). *)
  (*       by split. *)
  (*     + rewrite /= in Mix; by rewrite Mix in C'.         *)
  (* Qed. *)

  (* Lemma Red_N' : *)
  (*   forall (y n : nat), *)
  (*     (forall (x1 :nat), Cpos x1 y red) -> (forall (x2 :nat), Cpos x2 (y + n) red). *)
  (* Proof. *)
  (*   move=> n y; by apply Red_N. *)
  (* Qed. *)

  (* ある段が全て赤ならその下はずっと赤 (Red_N と似ているが，x の範囲制限つき) *)  
  Lemma AllRedN :
    forall x y n : nat,
      (forall i :nat, (0 <= i <= n -> Cpos (x+i) y red))
      -> forall q p : nat, (0 <= p+q <= n ->  Cpos (x+p) (y+q) red). 
  Proof.
    move=> x y n topcolor.
    induction q.
    - (* base case: q is 0 *)
      move=> p. 
      rewrite ! addn0. apply topcolor. 
    - (* induction case: q is successor *)
      move=> p. move/andP. move =>[rangePQ1 rangePQ2].
      + have prevL: Cpos (x+p) (y+q) red.
        apply IHq.
        apply /andP. apply conj. done.
        rewrite addnS in rangePQ2. by apply ltnW. 
      + have prevR: Cpos ((x+p).+1) (y+q) red.
        rewrite- (addnS x p). 
        apply IHq. apply /andP. apply conj. done. 
        rewrite addSn. rewrite addnS in rangePQ2. done.
    - have [c Red'] : exists c : Color, Cpos (x+p) (y+q+1) c.
        by apply C_exists.
    - have Mix : c = mix red red.
      rewrite- addn1 in prevR. 
      rewrite- addn1 in Red'. apply (C_mix (x+p) (y+q)). by split. 
    - rewrite /= in Mix. rewrite- Mix. rewrite addnS. rewrite- addn1. done. 
  Qed.

  (* ある段が全て赤なら最下段も赤 *)
  Lemma AllRed:
    forall x y n : nat,
      (forall i :nat, (0 <= i <= n -> Cpos (x+i) y red)) -> Cpos x (y+n) red. 
  Proof.
    move=> x y n topcolor.
    have fromAllRedN: forall q p : nat, (0 <= p+q <= n ->  Cpos (x+p) (y+q) red). by apply AllRedN. 
    generalize (fromAllRedN n 0). rewrite addn0. rewrite add0n. move=> A. apply A.
    apply/andP. done. 
  Qed.

  (* Three_Color_Triangle_Problem_nec_even のための定義と補題群 *)
  (* colorYB x n k z : 最上段の x から x+n までのマスを黄，青と交互に塗る (範囲外は黄にする) *)
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
    forall x y n : nat, n > 0 ->
    (forall i : nat, ((0 <= i <= n) -> Cpos (x+i) y (colorYB x n (x+i)))) ->
             forall i : nat, ((0 <= i <= n.-1) -> Cpos (x+i) (y+1) red).
  Proof.
    move=> x y n NotZero topcolor i range.
    
    (* 最上段のマスが colorYB で塗られていることを示す *)
    - have rangetop1 : 0 <= i <= n.
      apply /andP. apply conj. done.
      move: range. move /andP. move=> [] rangetop1a rangetop1b.
      apply (trans_lelele rangetop1b). apply leq_pred.
      generalize (topcolor i) => Cpos1. specialize (Cpos1 rangetop1).
    - have rangetop2 : 0 <= i.+1 <= n.
      apply /andP. apply conj. done.
      move: range. move /andP. move=> [] rangetop2a rangetop2b.
      have S_pred : (i.+1 <= n) = (i <= n.-1).
      apply ceql_S_le_le_P. done.
      rewrite S_pred. done. rewrite- addn1 in rangetop2.
      generalize (topcolor (i+1)) => Cpos2. specialize (Cpos2 rangetop2).

    (* 最上段より 1 段下のマスの色は mix と colorYB で得られることを示す *)
    - have Cpos3 : exists c : Color, Cpos (x+i) (y+1) c.
      apply C_exists. move: Cpos3. case. move=> c Cpos3.
      have Color : c = mix (colorYB x n (x + i)) (colorYB x n (x + (i + 1))).
      apply (C_mix (x+i) y).
      apply conj. done. apply conj. rewrite- addnA. done. done.
      rewrite Color in Cpos3.

    (* colorYB で塗られている色を示す *)
    - case (odd_or_even i) => [OddI|EvenI].
      
    (* i が奇数のとき *)
      + have Color1 : colorYB x n (x + i) = blu.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangetop1 OddI. done.
      + have Color2 : colorYB x n (x + (i + 1)) = yel.
        have OddI1 : odd (i+1) = false.
        rewrite addn1 OddS. by rewrite OddI.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangetop2 OddI1. done.
      + rewrite Color1 Color2 in Cpos3. by rewrite /= in Cpos3.
        
    (* i が偶数のとき *)
      + have Color1 : colorYB x n (x + i) = yel.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangetop1 EvenI. done.
      + have Color2 : colorYB x n (x + (i + 1)) = blu.
        have OddI1 : odd (i+1) = true.
        rewrite addn1 OddS. by rewrite EvenI.
        rewrite /colorYB. rewrite x_plus_y_minus_x_is_y.
        rewrite rangetop2 OddI1. done.
      + rewrite Color1 Color2 in Cpos3. by rewrite /= in Cpos3.
  Qed.
  
  Lemma EvenB :
    forall x y n : nat, n > 0 ->
    (forall i : nat, ((0 <= i <= n) -> Cpos (x+i) y (colorYB x n (x+i)))) -> Cpos x (y+n) red.
  Proof.
    move=> x y n NotZero topcolor.
    have AllRed1 : forall i : nat, (0 <= i <= n.-1) -> Cpos (x+i) (y+1) red.
    apply EvenA. done. done.
    have YN : y + n = (y + 1) + (n - 1).
    rewrite addnAC. rewrite- addnA. rewrite subn1 addn1.
    have pred_S : n.-1.+1 = n.
    apply prednK. done. rewrite pred_S. done. rewrite YN.
    apply AllRed. by rewrite subn1.
  Qed.

  Lemma Three_Color_Triangle_Problem_nec_even :
    forall x y n :nat,
      (n > 0) && (odd n == false) ->
      ~(forall c:Color, forall f:nat -> Color, Triangle x y n (f x) (f (x+n)) c).
  Proof.
    move=> x y n.
    move /andP; move=> [] NotZeroN OddN Triangle_hyp.
    have topcolor : forall i : nat, ((0 <= i <= n) -> Cpos (x+i) y (colorYB x n (x+i))).
    move=> i range. by apply C_paint.

    (* 最下段のマスの色が異なることで矛盾を導く *)
    
    (* EvenB より最下段のマスの色が red であることを示す．*)
    - have CposR : Cpos x (y+n) red. by apply EvenB.

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
    - have : exists c : Color, Cpos x (y+n) c. apply C_exists.
      case. move=> c CposY.
      generalize (Triangle_hyp c (colorYB x n)) => TriangleN.
      have ColorBelow : c = mix (colorYB x n x) (colorYB x n (x + n)).
      apply TriangleN. apply conj. rewrite addn0 in Cpos0. done. done.

    (* CposY の色が yel であることを示す *)
    - have sameColor : colorYB x n x = colorYB x n (x + n).
      apply lemYB3; done. rewrite- sameColor in ColorBelow.
      have ColorY : colorYB x n x = yel.
      rewrite /colorYB. rewrite x_minus_x_is_0. by rewrite range0a.
      rewrite ColorY in ColorBelow. rewrite /= in ColorBelow.
      rewrite ColorBelow in CposY.

    (* falseColor より矛盾を示す *)
    - apply (falseColor x (y+n) red yel).
      apply conj. done. apply conj. done. done.  
  Qed.
      
  (* Lemma Three_Color_Triangle_Problem_nec_even : *)
  (*   forall n x y: nat, *)
  (*     (1 <= n) -> *)
  (*     (exists k, n = 2 * k) -> *)
  (*     ((forall (x1 : nat), (exists k1, x1 = 2 * k1) -> Cpos x1 y blu) /\ *)
  (*     (forall (x2 : nat), (exists k2, x2 = 2 * k2 + 1) -> Cpos x2 y yel)) -> *)
  (*     ( ~ (exists k :nat, n = 3 .^ k) -> ~ forall (c0 c1 c2 : Color),((Cpos x y c0 /\ Cpos (x + n) y c1 /\ Cpos x (y + n) c2) -> c2 = mix c0 c1)). *)
  
  (* Proof. *)
  (*   (* move=> n; case n. *) *)
  (*   (* - by move=> x y c0 c1 c2 Even.  *) *)
  (*   move=> n x y. *)
  (*   move=> NotZero_N Even_N Paint Not3k Triangle. *)
  (*   destruct Even_N as [m]; move: H => Even_N. *)
  (*   have Alternate : *)
  (*     ((forall (x1 : nat), (exists k1, x1 = 2 * k1) -> Cpos x1 y blu) /\ (forall (x2 : nat), (exists k2, x2 = 2 * k2 + 1) -> Cpos x2 y yel)) -> *)
  (*     (forall (x : nat), Cpos x (y + 1) red). *)
  (*   by apply Paint_Alternate. *)
  (*   specialize (Alternate Paint). *)
  (*   destruct Paint as [Paint_Even Paint_Odd]. *)
  (*   - have Red_Y1 : *)
  (*       (forall x1 : nat, Cpos x1 y red) -> forall (x2 : nat), Cpos x2 (y + 1) red. *)
  (*     by apply Red_N. *)
  (*   - have Red_YN : *)
  (*       (forall x1 : nat, Cpos x1 (y + 1) red) -> forall (x2 : nat), Cpos x2 (y + n) red. *)
  (*     move=> Paint_Red_Y1. *)
  (*     apply Red_N. *)
  (*   - have Red_Y1N : *)
  (*       (forall x1 : nat, Cpos x1 (y + 1) red) -> forall (x2 : nat), Cpos x2 (y + 1 + n) red. *)
  (*     by apply Red_N. *)
  (*     (* specialize(Red_Y1N Alternate). *) *)
  (*     (* + have N' : exists n' : nat, n = n' + 1. *) *)
  (*     (*   exists ((2 * m) - 1). *) *)
  (*     (*   rewrite- Even_N. *) *)
  (*       * have NotZero_M : m <> 0. *)
  (*         move=> mZero. *)
  (*         rewrite mZero in Even_N. *)
  (*         rewrite muln0 in Even_N. *)
  (*         rewrite Even_N in NotZero_N. *)
  (*         by []. *)
  (*       * have notZero_N : n <> 0. *)
  (*         move=> Zero_N. *)
  (*         rewrite Zero_N in Even_N. *)
  (*       * have Zero_M : m = 0. *)
  (*         * have tmp : Nat.div2 (2 * m) = m. *)
  (*           by apply Nat.div2_double. *)
  (*         rewrite- Even_N in tmp. *)
  (*         by []. *)
  (*       by []. *)
  (*   + have N' : exists n' : nat, n = n' + 1. *)
  (*       exists ((2 * m) - 1). *)
  (*       rewrite- Even_N. *)
  (*       rewrite addn1; rewrite subn1. *)
  (*       symmetry. *)
  (*     by rewrite  prednK. *)

  (*     destruct N' as [n' N']. *)

      
    (* rewrite [n'+1]addnC; rewrite addnA. *)
    (*   by apply Red_Color0N'_Y. *)
    (*   specialize (Red_Color01' Alternate). *)
    (*   have Cpos_Below : Cpos x (y + n) red. *)
    (*   by apply Red_Color01'. *)

    (*   (* Cpos x (y+n) red を示す *) *)
    (*   have Paint_Red_YN : Cpos x (y + n) red. *)
    (*   by apply Red_YN. *)
    (*   have Red_YN' : Cpos (x + 1) (y + n) red. *)
    (*   by apply Red_N. *)
    (*   have Red_YN1 : exists c : Color, Cpos x (y + n + 1) c. *)
    (*   by apply C_exists. *)
    (*   destruct Red_YN1 as [c' Red_YN1]. *)
    (*   have Red_Mix : c' = mix red red. *)
    (*   apply (C_mix x2 (y + n)). *)
    (*   by split. *)
    (*   rewrite /= in Mix; by rewrite Mix in C'. *)
    (*   specialize (Red_Color01' Alternate). *)
    (*   move : Red_Color. *)
    (*   rewrite- addnA. rewrite [1 + n]addnC. rewrite [n + 1]addn1. *)
    (*   move => Red_Color. *)
    (*   have Color_Below : Cpos x (y + n) red. *)
    (*   by apply Red_Color. *)

    (* * have NotZero_M : m <> 0. *)
    (*       move=> mZero. *)
    (*       rewrite mZero in Even_N. *)
    (*       rewrite muln0 in Even_N. *)
    (*       rewrite Even_N in NotZero_N. *)
    (*       by []. *)
    (*     * have notZero_N : n <> 0. *)
    (*       move=> Zero_N. *)
    (*       rewrite Zero_N in Even_N. *)
    (*     * have Zero_M : m = 0. *)
    (*       * have tmp : Nat.div2 (2 * m) = m. *)
    (*         by apply Nat.div2_double. *)
    (*       rewrite- Even_N in tmp. *)
    (*       by []. *)
    (*     by []. *)
            
    (* case (even_or_odd x) => [Even_X|Odd_X]. *)
    
    (* (* x:even の場合開始 *) *)
    (* - move: Even_X. *)
    (*   rewrite even_equiv; rewrite /Nat.Even. *)
    (*   move=> Even_X. *)
    (*   destruct Even_X as [m' Even_X]. *)
    (*   rewrite- coqnat_mult in Even_X. *)

    (*   (* Cpos x (y + n) red を示す *) *)
    (*   have Paint_Red_YN : Cpos x (y + n) red. *)
    (*   rewrite Even_N. *)
    (*   rewrite addnA. *)
    (*   apply Red_N. *)
      
      
    (*   (* even x と n = 2 * m より even( x + n ) を示す *) *)
    (*   + have Even_XN : even(x + n). *)
    (*     apply even_even_plus. *)
    (*     * rewrite even_equiv; rewrite /Nat.Even. *)
    (*       by exists m'. *)
    (*     * rewrite even_equiv; rewrite /Nat.Even. *)
    (*       exists m. *)
    (*       by rewrite- coqnat_mult. *)
            
    (*   (* Cpos (x + n) y blue を示す *)       *)
    (*   + have Blue_Y' : Cpos (x + n) y blu. *)
    (*     apply Paint_Even. *)
    (*     move: Even_XN. *)
    (*     rewrite even_equiv; rewrite /Nat.Even. *)
    (*     move=> Even_XN. *)
    (*     destruct Even_XN as [k Even_XN]. *)
    (*     rewrite- coqnat_mult in Even_XN. *)
    (*     by exists k.  *)

    (*   (* Triangle から Cpos x (y + n) blu を示す *) *)
    (*   + have Blue_Y : Cpos x y blu. *)
    (*     apply Paint_Even. *)
    (*     by exists m'. *)
    (*   + have Blue_YN : exists c : Color, Cpos x (y + n) c. *)
    (*     by apply C_exists. *)
    (*     destruct Blue_YN as [c' Blue_YN].  *)
    (*   + have Mix : c' = mix blu blu. *)
    (*     apply Triangle. *)
    (*     by split.   *)

    (*   (* Cpos x (y + n) blu と Cpos x (y + n) red から矛盾を示す *) *)
    (*   rewrite /= in Mix; rewrite Mix in Blue_YN. *)
      
    (*   (* (x : even の場合終了) *) *)

    (*   (* x:odd の場合開始 *) *)
    (*   (* Cpos x (y+n) red を示す *) *)
      
    (*   (* odd x と Paint_Odd より Cpos x y yel を示す *) *)
      
    (*   (* odd x と n = 2 * m より odd(x+n)を示す *) *)
    (*   + have Odd_XN : odd(x + n). *)
    (*     apply odd_plus_l. *)
    (*     * rewrite odd_equiv; rewrite /Nat.Odd. *)
    (*       exists m'. *)
    (*     * rewrite even_equiv; rewrite /Nat.Even. *)
    (*       exists m. *)
    (*       by rewrite- coqnat_mult. *)
            
    (*   (* Cpos (x+n) y yel を示す *) *)
    (*   + have Yellow_Y' : Cpos (x + n) y yel. *)
    (*     apply Paint_Odd. *)
    (*     move: Odd_XN. *)
    (*     rewrite odd_equiv; rewrite /Nat.Odd. *)
    (*     move=> Odd_XN. *)
    (*     destruct Odd_XN as [k Odd_XN]. *)
    (*     rewrite- coqnat_mult in Od_XN. *)
    (*     by exists k. *)
                    
    (*   (* Triangle より Cpos x (y+n) yel を示す *) *)
    (*   + have Yellow_Y : Cpos x y yel. *)
    (*     apply Paint_Odd. *)
    (*     by exists m'. *)
    (*   + have Yellow_YN : exists c : Color, Cpos x (y + n) c. *)
    (*     by apply C_exists. *)
    (*     destruct Yellow_YN as [c' Yellow_YN].  *)
    (*   + have Mix : c' = mix yel yel. *)
    (*     apply Triangle. *)
    (*     by split. *)
          
    (*   (* これと Cpos x (y+n) red より矛盾を示す *) *)
    (*   rewrite /= in Mix; rewrite Mix in Yelloe_YN. *)
  (* (x : odd の場合終了) *)

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
  Lemma lemYBBY5: forall x n i: nat, (odd n == true) -> colorYBBY x n x = colorYBBY x n (x+n).
  Proof.
    move=> x n i.  move /eqP => oddN.
    rewrite /colorYBBY. rewrite subnn.
    - have range0 : (0 <= 0 <= n./2) && (ssrnat.odd 0 == false).
      rewrite /=. done.
      rewrite range0.
    - rewrite (x_plus_y_minus_x_is_y x n). rewrite oddN.
      have rangeN1 : ((0 <= n <= n./2) && (true == false)) = false.
      rewrite andbF. done. rewrite rangeN1.
    - have rangeN2 : n./2.+1 <= n <= n.
      apply /andP. apply conj. apply leq_half2. by rewrite oddN. apply leqnn.
      rewrite rangeN2. by rewrite /=.
  Qed.

  Lemma ShortOddA :
    forall x y n k : nat,
      ((3.^k <= n <= (3.^k).*2) && (odd n == true)) ->
      (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle x1 y1 (3 .^ k) c0 c1 c2) ->
      (forall i : nat, ((0 <= i <= n) -> Cpos (x+i) y (colorYBBY x n (x+i)))) ->
      (forall i : nat, ((0 <= i <= n - 3.^k) -> Cpos (x+i) (y+3.^k) (colorYB x (n-3.^k) (x+i)))).
  Proof.
    move=> x y n k. move/andP. case=>[A B]. move:(A). move/andP. case=>[A1 A2]. move=>triangle color i rangeI.
    move:{+} rangeI. move/andP. case=>[rangeI1 rangeI2].
    - have A3: n < (3.^k).*2. rewrite eq_le_eq_lt in A2. move:A2. move/orP. case. move=>P.
      have B': odd ((3.^k).*2). move/eqP in P. rewrite- P. move/eqP in B. done. rewrite odd_double in B'. done. done.
    - have B': odd n = true. by apply/eqP.      
    - have C1: 1+(n./2).*2 = n. rewrite- {2} (odd_double_half n). rewrite B'. done.
    - have C2: (n./2).*2 = n.-1. apply/eqP. rewrite- eq_adjoint_S_P_eq. apply/eqP. done. by apply odd_gt0.
    - have C3: n-(n./2) = (n./2).+1. apply/eqP. rewrite eq_adjoint_minus_plus_eq. apply/eqP.
      rewrite- addn1. rewrite eq_comm_plus. rewrite- eq_assoc_plus. rewrite addnn. by rewrite eq_comm_plus.
      apply leq_half1.
    - have C4: n./2 < 3.^k. by rewrite eq_adjoint_half_double_lt.
    - have C5: n-3.^k <= n./2. rewrite eq_adjoint_minus_plus_le. rewrite eq_comm_plus.
      rewrite- eq_adjoint_minus_plus_le. rewrite C3. done. 
    - have C6: i<=n./2. apply (trans_lelele rangeI2). done.
    - have C7: n./2 < i + 3 .^ k. apply (trans_ltlelt C4). rewrite eq_comm_plus. apply leq_addr. 
    - have C8: i + 3 .^ k <= n. by rewrite eq_adjoint_plus_minus_le.
    - have C9: odd (3.^k). by apply odd3m. 
    - have rangeIa: 0 <= i <= n.
      apply/andP; split. done. apply (trans_lelele rangeI2); apply leq_subr.
    - have rangeIb: 0 <= (i+3.^k) <= n.
      apply/andP; split. apply (trans_lelele rangeI1); apply leq_addr. by rewrite (eq_adjoint_plus_minus_le i A1).
    - have posN: 0<n. by apply odd_gt0.
    - have Cpos1: Cpos (x+i) y (colorYBBY x n (x+i)).
      apply color; apply rangeIa.
    - have Cpos2: Cpos (x+i+3.^k) y (colorYBBY x n (x+i+3.^k)).
      rewrite eq_assoc_plus. apply color. apply rangeIb.      
    - have [c' Cpos3]: exists c:Color, Cpos (x+i) (y+3.^k) c. by apply C_exists.
    - have mix: c' = mix (colorYBBY x n (x+i)) (colorYBBY x n (x+i+3.^k)).
      by apply (triangle (x+i) y (colorYBBY x n (x+i)) (colorYBBY x n (x+i+3.^k))).
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
    forall x y n k : nat,
      ((3.^k <= n <= (3.^k).*2) && (odd n == true)) ->
      (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle x1 y1 (3 .^ k) c0 c1 c2) ->
      (forall i : nat, ((0 <= i <= n) -> Cpos (x+i) y (colorYBBY x n (x+i)))) ->
      (forall i : nat, ((0 <= i <= (n - 3.^k).-1) -> Cpos (x+i) ((y+3.^k).+1) red)).
  Proof.
    
  Admitted.

  Lemma ShortOddC :
    forall x y n k : nat,
      ((3.^k <= n <= (3.^k).*2) && (odd n == true)) ->
      (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle x1 y1 (3 .^ k) c0 c1 c2) ->
      (forall i : nat, ((0 <= i <= n) -> Cpos (x+i) y (colorYBBY x n (x+i)))) ->
      Cpos x (y+n) red.
  Proof.
    
  Admitted.

  Lemma Three_Color_Triangle_Problem_nec_oddA :
    forall x y n k : nat,
      ((3.^k <= n <= (3.^k).*2) && (odd n == true)) ->
      ~(forall c:Color, forall f:nat -> Color, Triangle x y n (f x) (f (x+n)) c).
  Proof.

  Admitted.

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
      rewrite eql_false. rewrite eql_dual_and. rewrite ! eql_dual_le.
      apply/orP. left. move: range. move/andP. move=> [A B].
      have H1: (0 < 3.^k) = true. by apply expn3Pos.
        by rewrite (ceql_S_le_le_P i H1).
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
      rewrite eql_false. rewrite eql_dual_and. rewrite ! eql_dual_le.
      apply/orP. right. move: range. move/andP. move=> [A B]. done.
    - by rewrite H in T.
  Qed.

  (* n の範囲条件から導かれる不等式 *)
  Lemma fromRangeN:
    forall k n : nat,
      ((3.^k).*2 + 1 <= n < (3.^(k.+1))) -> ((3.^k) <= n) /\ ((3.^k).*2 <= n) /\ (n - (3.^k).*2 <= (3.^k).-1).
  Proof.
    move => k n. move/andP. move=> [rangeN1 rangeN2]. apply conj. 
    - (* first goal *)
      have X1: ((3.^k) <= (3.^k).*2 + 1).
      rewrite- addnn. rewrite eql_assoc_plus. rewrite- eql_le_plus_l. by apply leq0n.
      by apply (trans_lelele X1).
    - (* second goal *)
      have X2: ((3.^k).*2 <= n). 
      apply ltnW. rewrite  addn1 in rangeN1. done.
      apply conj. done. 
    - (* third goal *)
      have X3: (0 < 3.^k) = true. by apply expn3Pos.
      rewrite- (ceql_S_le_le_P (n - (3 .^ k).*2) X3). 
      rewrite (ceql_minus_lt_lt_plus_l (3 .^ k) X2).
      rewrite expnS in rangeN2.
      rewrite (mulnDr' 1 2 (3.^k)) in rangeN2.
      rewrite mul2n in rangeN2. 
      rewrite mul1n in rangeN2.
      rewrite eql_comm_plus. done. 
  Qed.

  (* (* ある段が全て赤ならその下はずっと赤 (Red_N と似ているが，x の範囲制限つき) *)   *)
  (* Lemma AllRedN : *)
  (*   forall x y n : nat, *)
  (*     (forall i :nat, (0 <= i <= n -> Cpos (x+i) y red)) *)
  (*     -> forall q p : nat, (0 <= p+q <= n ->  Cpos (x+p) (y+q) red).  *)
  (* Proof. *)
  (*   move=> x y n topcolor. *)
  (*   induction q. *)
  (*   - (* base case: q is 0 *) *)
  (*     move=> p.  *)
  (*     rewrite ! addn0. apply topcolor.  *)
  (*   - (* induction case: q is successor *) *)
  (*     move=> p. move/andP. move =>[rangePQ1 rangePQ2]. *)
  (*     + have prevL: Cpos (x+p) (y+q) red. *)
  (*       apply IHq. *)
  (*       apply /andP. apply conj. done. *)
  (*       rewrite addnS in rangePQ2. by apply ltnW.  *)
  (*     + have prevR: Cpos ((x+p).+1) (y+q) red. *)
  (*       rewrite- (addnS x p).  *)
  (*       apply IHq. apply /andP. apply conj. done.  *)
  (*       rewrite addSn. rewrite addnS in rangePQ2. done. *)
  (*   - have [c Red'] : exists c : Color, Cpos (x+p) (y+q+1) c. *)
  (*       by apply C_exists. *)
  (*   - have Mix : c = mix red red. *)
  (*     rewrite- addn1 in prevR.  *)
  (*     rewrite- addn1 in Red'. apply (C_mix (x+p) (y+q)). by split.  *)
  (*   - rewrite /= in Mix. rewrite- Mix. rewrite addnS. rewrite- addn1. done.  *)
  (* Qed. *)

  (* (* ある段が全て赤なら最下段も赤 *) *)
  (* Lemma AllRed: *)
  (*   forall x y n : nat, *)
  (*     (forall i :nat, (0 <= i <= n -> Cpos (x+i) y red)) -> Cpos x (y+n) red.  *)
  (* Proof. *)
  (*   move=> x y n topcolor. *)
  (*   have fromAllRedN: forall q p : nat, (0 <= p+q <= n ->  Cpos (x+p) (y+q) red). by apply AllRedN.  *)
  (*   generalize (fromAllRedN n 0). rewrite addn0. rewrite add0n. move=> A. apply A. *)
  (*   apply/andP. done.  *)
  (* Qed. *)
  
  Lemma LongOddA:
    forall (k n x y : nat),
      ((3.^k).*2 + 1 <= n < (3.^(k.+1))) ->
      (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle x1 y1 (3 .^ k) c0 c1 c2) ->
      (forall i: nat,(0 <= i <= n -> Cpos (x+i) y (colorBYB x n k (x+i)))) -> 
      (
        (forall i: nat,(0 <= i <= n - (3.^k).*2 -> Cpos (x+i) (y+3.^k) red))
        /\
        (forall i: nat,(3.^k <= i <= n - 3.^k -> Cpos (x+i) (y+3.^k) red))
      ).
  Proof.
    - move=> k n x y rangeN triangle topcolor.
      + have A1: (3.^k) <= n. by apply fromRangeN.
      + have A2: (3 .^ k).*2 <= n. by apply fromRangeN.
      + have A3: n - (3.^k).*2 <= (3.^k).-1. by apply fromRangeN.
      + have exp3Pos: (0 < 3.^k) = true. by apply expn3Pos.    
        apply conj.
      + (* first part *)
        move=> i. move /andP. move => [C D].
      + have E: 0 <= i <= n.
        apply /andP. apply conj. done.
        apply (trans_lelele D), leq_subr.
      + have A4: 0 <= i <= (3.^k).-1.
        apply/andP. apply conj. done. apply (trans_lelele D A3).
      + have CposB: Cpos (x+i) y blu. 
        ++ have colB: colorBYB x n k (x+i) = blu. apply (lemBYB1 x y n k i A4).
        ++ rewrite- colB. by apply C_paint. 
      + have CposY: Cpos (x+(3.^k)+i) y yel.
        ++ have A5: 3.^k <= (3.^k)+i <= n-(3.^k).
           apply /andP. apply conj. by rewrite- eql_le_plus_l.
           rewrite- (ceql_plus_le_le_minus_r ((3.^k)+i) A1).
           rewrite- eql_assoc_plus. rewrite addnn.
             by rewrite (ceql_plus_le_le_minus_r i A2).
        ++ have colY: colorBYB x n k (x+(3.^k)+i) = yel.
           rewrite eql_assoc_plus. apply (lemBYB2 x y n k ((3.^k)+i) A5).
        ++ rewrite- colY. by apply C_paint. 
      + have CposR: Cpos (x+i) (y+(3.^k)) red.
        have mixR: red = mix blu yel. done. 
        rewrite mixR.
        apply Bottom_color_of_triangle. done. done.
        rewrite eql_assoc_plus. rewrite (eql_comm_plus i (3.^k)). rewrite- eql_assoc_plus. done.
        done.
      + (* second part *)
        move=> i. move /andP. move => [C D].      
      + have E: 0 <= i <= n.
        apply /andP. apply conj. done.
        apply (trans_lelele D), leq_subr.
      + have A4: 3.^k <= i <= n-(3.^k).
        apply/andP. apply conj. done. done. 
      + have CposY: Cpos (x+i) y yel. 
        ++ have colY: colorBYB x n k (x+i) = yel. apply (lemBYB2 x y n k i A4).
        ++ rewrite- colY. by apply C_paint. 
      + have CposB: Cpos (x+(3.^k)+i) y blu.
        ++ have A5: n - 3 .^ k < 3 .^ k + i <= n. 
           apply /andP. apply conj.
           rewrite (ceql_minus_lt_lt_plus_r (3.^k+i) A1).
           rewrite (eql_comm_plus (3.^k) i).
           have X: n < 3 .^ k.+1. move: rangeN. move/andP. move=>[rangeN1 rangeN2]. done.
           apply (trans_ltlelt X). rewrite expnS. 
           rewrite (mulnDr' 1 2 (3.^k)). 
           rewrite mul1n. rewrite mul2n. rewrite eql_assoc_plus. rewrite addnn.
           rewrite- (eql_mono_plus_le_plus (3.^k) i). done. 
           have Y: i <= n - 3 .^ k. done.
           rewrite- (ceql_plus_le_le_minus_l i A1) in Y.
           rewrite eql_comm_plus. done.
        ++ have colB: colorBYB x n k (x+(3.^k)+i) = blu.
           rewrite eql_assoc_plus. apply (lemBYB3 x y n k ((3.^k)+i)). done. 
        ++ rewrite- colB. by apply C_paint.            
      + have CposR: Cpos (x+i) (y+(3.^k)) red.
        have mixR: red = mix yel blu. done. 
        rewrite mixR.
        apply Bottom_color_of_triangle. done. done. 
        rewrite eql_assoc_plus. rewrite (eql_comm_plus i (3.^k)). rewrite- eql_assoc_plus. done.
        done.
  Qed.
  
  Lemma LongOddB:
    forall (k n x y : nat),
      ((3.^k).*2 + 1 <= n < (3.^(k.+1))) ->
      (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle x1 y1 (3 .^ k) c0 c1 c2) ->
      (forall i: nat,(0 <= i <= n -> Cpos (x+i) y (colorBYB x n k (x+i)))) ->
      forall i:nat, (0 <= i <= n-(3.^k).*2) -> Cpos (x+i) (y+(3.^k).*2) red. 
  Proof.
    - move=> k n x y rangeN triangle color i rangeI.
      + have A1: (3.^k) <= n. by apply fromRangeN. 
      + have A2: (3 .^ k).*2 <= n. by apply fromRangeN.
      + have A3: n - (3.^k).*2 <= (3.^k).-1. by apply fromRangeN.
      + have exp3Pos: (0 < 3.^k) = true. by apply expn3Pos.    
      + have [fromA1 fromA2]: 
          (forall i: nat,(0 <= i <= n - (3.^k).*2 -> Cpos (x+i) (y+3.^k) red))
          /\ (forall i: nat,(3.^k <= i <= n - 3.^k -> Cpos (x+i) (y+3.^k) red)). by apply LongOddA.
      + have CposR1: Cpos (x+i) (y+3.^k) red.
        apply fromA1. done.
      + have CposR2: Cpos (x+i) (y+(3.^k).*2) red.
      + have mixR: red = mix red red. done.
      + rewrite mixR. rewrite- addnn. rewrite- (eql_assoc_plus y (3.^k) (3.^k)).
        apply Bottom_color_of_triangle. done. done. rewrite (eql_assoc_plus x i (3.^k)). apply fromA2.
        apply /andP. rewrite- (eql_le_plus_r (3.^k) i). apply conj. done.
        rewrite- (ceql_plus_le_le_minus_l (i+3.^k) A1).
        rewrite eql_assoc_plus. rewrite addnn.
        move:rangeI. move/andP. move =>[P Q].
          by rewrite (ceql_plus_le_le_minus_l i A2).
          done.
  Qed.
  
  Lemma LongOddC:
    forall (k n x y : nat),
      ((3.^k).*2 + 1 <= n < (3.^(k.+1))) ->
      (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle x1 y1 (3 .^ k) c0 c1 c2) ->
      Cpos x (y+n) red. 
  Proof.
    - move=> k n x y rangeN triangle.
      + have rangeN1: (3 .^ k).*2 <= n.
          by apply fromRangeN.
      + have fromB: forall i:nat, (0 <= i <= n-(3.^k).*2 -> Cpos (x+i) (y+(3.^k).*2) red).
        apply LongOddB. done. done.
        move=> i rangeI. apply C_paint.
      + have fromRR: Cpos x (y + (3 .^ k).*2 + (n - (3 .^ k).*2)) red.
        apply (AllRed x (y+(3.^k).*2) (n-((3.^k).*2))). done. 
        rewrite eql_assoc_plus in fromRR.
        rewrite (addnBA ((3.^k).*2) rangeN1) in fromRR.
        rewrite x_plus_y_minus_x_is_y in fromRR. done. 
  Qed.

  (* 奇数の場合-2 終わり *)
  Lemma Three_Color_Triangle_Problem_nec_oddB :
    forall (x y n k : nat),
      ((3.^k).*2 + 1 <= n < (3.^(k.+1))) ->
      ~(forall c:Color, forall f:nat -> Color, Triangle x y n (f x) (f (x+n)) c).
  Proof.
    - move=> x y n k rangeN triangle.
      + have A1: (3.^k) <= n. by apply fromRangeN.
      + have tri3k: forall x y: nat, forall c0 c1 c2: Color, Triangle x y (3.^k) c0 c1 c2.
        move=> x1 y1 c0 c1 c2. apply Three_Color_Triangle_Problem_suf. exists k. done. 
      + have CposBYB: forall i:nat, 0<=i<=n -> Cpos (x+i) y (colorBYB x n k (x+i)).
        move=> i rangeI. apply C_paint. 
      + have CposR: Cpos x (y+n) red.
        by apply (LongOddC k n x y).
      + have triBYB: Triangle x y n (colorBYB x n k x) (colorBYB x n k (x+n)) red. done. 
      + have colB1: colorBYB x n k x = blu.
        rewrite- {2} (addn0 x). 
        apply (lemBYB1 x y). done. 
      + have colB2: colorBYB x n k (x+n) = blu.
        apply (lemBYB3 x y). apply/andP. apply conj. 
        rewrite (ceql_minus_lt_lt_plus_l n A1).
        rewrite- (eql_lt_plus_r n (3.^k)). apply expn3Pos. done. 
      + have triBBR: Triangle x y n blu blu red.
        rewrite- {1} colB1. rewrite- {1} colB2. done.
      + have CposB1: Cpos x y blu.
        rewrite- colB1. rewrite- {1 3} (addn0 x). apply CposBYB. done. 
      + have CposB2: Cpos (x+n) y blu.
        rewrite- colB2. apply CposBYB. apply/andP. done. 
      + have mixRBB: red = mix blu blu.
        apply triBBR. apply conj. done. done. done.         
  Qed.

  
  Lemma Three_Color_Triangle_Problem_nec' :
    forall (n x y : nat), n > 0 ->
      ~(exists k :nat, n = 3 .^ k) -> ~(forall c:Color, forall f:nat -> Color, Triangle x y n (f x) (f (x+n)) c).
  Proof.
    move=> n x y NotZeroN_hyp Notexp3k.
    case (rangeN n) => k rangeN; case rangeN => [ZeroN|NotZeroN].
    - rewrite ZeroN in NotZeroN_hyp. done.
    - case (odd_or_even n) => [OddN|EvenN].
      + case NotZeroN => [Short|Long].
        * apply (Three_Color_Triangle_Problem_nec_oddA x y n k).
          apply /andP. apply conj. done. apply /eqP. done.
        * apply (Three_Color_Triangle_Problem_nec_oddB x y n k). done.
      + apply (Three_Color_Triangle_Problem_nec_even).
        apply /andP. apply conj. done. apply /eqP. done.
 Qed.
    

  Theorem Three_Color_Triangle_Problem_nec :
    forall (n x y : nat), n > 0 ->
      (forall c0 c1 c2 : Color, Triangle x y n c0 c1 c2) ->
      (exists k :nat, n = 3 .^ k).
  Proof.
    move=> n x y NotZeroN_hyp.

    (* 対偶を用いて示す *)
    apply Contraposition. move=> Notexp3k.

    (* "調和三角形の塗り方が存在しない" <-> "調和三角形が存在しない" *)
    have T :
      ~(forall c:Color, forall f:nat ->Color, Triangle x y n (f x) (f (x+n)) c) <->
      ~ (forall c0 c1 c2 : Color, Triangle x y n c0 c1 c2).
    apply conj.
    - rewrite- Contraposition. move=> Triangle_hyp c f.
      generalize (Triangle_hyp (f x) (f (x + y)) c) => TriangleN. done.
    - move=> Triangle_hyp. by apply Three_Color_Triangle_Problem_nec'.

    (* Three_Color_Triangle_Problem_nec' を用いて示す *)
    apply T. apply Three_Color_Triangle_Problem_nec'. done. done.    
  Qed.

End Three_Color_Triangle_Problem_nec.



Section Three_Color_Triangle_Problem.

  Theorem Three_Color_Triangle_Problem_sufnec :
    forall (n x y : nat) , n > 0 ->
      (exists k : nat, n = 3 .^ k) <->
      (forall (c0 c1 c2 : Color), Triangle x y n c0 c1 c2).
  Proof.
    move=> n x y NotZeroN. apply conj.
    - by apply Three_Color_Triangle_Problem_suf.
    - by apply Three_Color_Triangle_Problem_nec.
  Qed.
  
  Theorem Three_Color_Triangle_Problem :
    forall (n : nat) , n > 0 ->
      (exists k :nat, n = 3 .^ k) <->
      (forall c0 c1 c2 : Color, Triangle 0 0 n c0 c1 c2).
  Proof.
    move=> n.
    by apply (Three_Color_Triangle_Problem_sufnec n 0 0).
  Qed.

End Three_Color_Triangle_Problem.
