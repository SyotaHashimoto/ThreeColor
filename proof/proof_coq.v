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

  Axiom C_conf :
    forall x y : nat, forall c0 c1 c2 : Color, Cconf c0 c1 c2 <-> (c0 = c1 /\ c1 = c2 /\ c2 = c0) \/ (c0 <> c1 /\ c1 <> c2 /\ c2 <> c0).
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
    forall (k n x y : nat) (c0 c1 c2 : Color), n = 3 .^ k -> ((Cpos x y c0 /\ Cpos (x + n) y c1 /\ Cpos x (y + n) c2)  -> c2 = mix c0 c1).
  Proof.
    elim=> [ | k IHk ].
    - move=> n x y c0 c1 c2 N0.
      rewrite expn0 in N0.
      rewrite N0.
      by apply C_mix.
    - move=> n x y c0 c1 c2 Nexp3k1 Cpos012.
      rewrite Nexp3k1 in Cpos012.
      destruct Cpos012 as [ Cpos0  H ].
      destruct H as [ Cpos1 Cpos2 ].
      
      (* マスに塗られている色に名前をつける *)
      * have: exists c : Color, Cpos (x + 3 .^ k) y c.
        by apply C_exists.
        case; move=> c3 Cpos3.
      * have: exists c : Color, Cpos (x + (2 * 3 .^ k)) y c.
        by apply (C_exists (x + (2 * 3 .^ k)) y).
        case; move=> c4 Cpos4.
      * have: exists c : Color, Cpos x (y + 3 .^ k) c.
        by apply (C_exists x (y + 3 .^ k)).
        case; move=> c5 Cpos5.
      * have: exists c : Color, Cpos (x + 3 .^ k) (y + 3 .^ k) c.
        by apply (C_exists (x + 3 .^ k) (y + 3 .^ k)).
        case; move=> c6 Cpos6.
      * have: exists c : Color, Cpos (x + (2 * 3 .^ k)) (y + 3 .^ k) c.
        by apply (C_exists (x + (2 * 3 .^ k)) (y + 3 .^ k)).
        case; move=> c7 Cpos7.
      * have: exists c : Color, Cpos x (y + (2 * 3 .^ k)) c.
        by apply (C_exists x (y + (2 * 3 .^ k))).
        case; move=> c8 Cpos8.
      * have: exists c : Color, Cpos (x + 3 .^ k) (y + (2 * 3 .^ k)) c.
        by apply (C_exists (x + 3 .^ k) (y + (2 * 3 .^ k))).
        case; move=> c9 Cpos9.

      (* 6 個の 3 .^ k 段の逆三角形 *)
      * have Tri0 : (Cpos x y c0 /\ Cpos (x + 3 .^ k) y c3 /\ Cpos x (y + 3 .^ k) c5) -> c5 = mix c0 c3.
        by apply IHk.
      * have Tri1 : (Cpos (x + 3 .^ k) y c3 /\ Cpos (x + (2 * 3 .^ k)) y c4 /\ Cpos (x + 3 .^ k) (y + 3 .^ k) c6) -> c6 = mix c3 c4.
        move=> Cpos346.
        apply (IHk (3 .^ k) (x + 3 .^ k) y).
        by [].
        rewrite- addnA; by rewrite add3n3n.
      * have Tri2 : (Cpos (x + 2 * 3 .^ k) y c4 /\ Cpos (x + 3 .^ (k.+1)) y c1 /\ Cpos (x + 2 * 3 .^ k) (y + 3 .^ k) c7) -> c7 = mix c4 c1.
        move=> Cpos417.
        apply (IHk (3 .^ k) (x + 2 * 3 .^ k) y).
        by [].
        rewrite- addnA.
        rewrite add23n3n.
        by [].
      * have Tri3 : (Cpos x (y + 3 .^ k) c5 /\ Cpos (x + 3 .^ k) (y + 3 .^ k) c6 /\ Cpos x (y + 2 * 3 .^ k) c8) -> c8 = mix  c5 c6.
        move=> Cpos568.
        apply (IHk (3 .^ k) x (y + 3 .^ k)).
        by [].
        rewrite- addnA.
        by rewrite add3n3n.
      * have Tri4 : (Cpos (x + 3 .^ k) (y + 3 .^ k) c6 /\ Cpos (x + 2 * 3 .^ k) (y + 3 .^ k) c7 /\ Cpos (x + 3 .^ k) (y + 2 * 3 .^ k) c9) -> c9 = mix c6 c7.
        move=> Cpos679.
        apply (IHk (3 .^ k) (x + 3 .^ k) (y + 3 .^ k)).
        by [].
        by do 2 rewrite- addnA; rewrite add3n3n.
      * have Tri5 : (Cpos x (y + 2 * 3 .^ k) c8 /\ Cpos (x + 3 .^ k) (y + 2 * 3 .^ k) c9 /\ Cpos x (y + 3 .^ (k.+1)) c2) -> c2 = mix c8 c9.
        move=> Cpos892.
        apply (IHk (3 .^ k) x (y + 2 * 3 .^ k)).
        by [].
        rewrite- addnA.
        by rewrite add23n3n.
      * have Cpos035: Cpos x y c0 /\ Cpos (x + 3 .^ k) y c3 /\ Cpos x (y + 3 .^ k) c5.
        by split.
      * have Cpos346: Cpos (x + 3 .^ k) y c3 /\ Cpos (x + 2 * 3 .^ k) y c4 /\ Cpos (x + 3 .^ k) (y + 3 .^ k) c6.
        by split.
      * have Cpos417: Cpos (x + 2 * 3 .^ k) y c4 /\ Cpos (x + 3 .^ (k.+1)) y c1 /\ Cpos (x + 2 * 3 .^ k) (y + 3 .^ k) c7.
        by split. 
      * have Cpos568: Cpos x (y + 3 .^ k) c5 /\ Cpos (x + 3 .^ k) (y + 3 .^ k) c6 /\ Cpos x (y + 2 * 3 .^ k) c8.
        by split.
      * have Cpos679: Cpos (x + 3 .^ k) (y + 3 .^ k) c6 /\ Cpos (x + 2 * 3 .^ k) (y + 3 .^ k) c7 /\ Cpos (x + 3 .^ k) (y + 2 * 3 .^ k) c9.
        by split.
      * have Cpos892: Cpos x (y + 2 * 3 .^ k) c8 /\ Cpos (x + 3 .^ k) (y + 2 * 3 .^ k) c9 /\ Cpos x (y + 3 .^ (k.+1)) c2.
        by split.
        
    (* それぞれの逆三角形における Cpos の関係から mix の関係を導く *)
      * have mix035 : c5 = mix c0 c3.
        by apply Tri0.
      * have mix346 : c6 = mix c3 c4.
        by apply Tri1.
      * have mix417 : c7 = mix c4 c1.
        by apply Tri2.
      * have mix568 : c8 = mix c5 c6.
        by apply Tri3.
      * have mix679 : c9 = mix c6 c7.
        by apply Tri4.
      * have mix892 : c2 = mix c8 c9.
        by apply Tri5.

      (* mixCut を用いて証明を完了させる *)
      rewrite mix568 mix679 in mix892;
      rewrite mix035 mix346 mix417 in mix892;
      rewrite mix892.
      apply mixCut.
  Qed.

  Theorem Three_Color_Triangle_Problem_suf :
    forall (x y n : nat),
      ((exists k : nat, n = 3 .^ k) -> forall (c0 c1 c2 : Color),(Triangle x y n c0 c1 c2)).
  Proof.
    move=> x y n eExp3k c0 c1 c2 Pos.
    case eExp3k.
    move=> k Exp3k.
    by apply (Three_Color_Triangle_Problem_suf' k n x y).
  Qed.
  
End Three_Color_Triangle_Problem_suf.

Section nat2.

  (* %Coq.Arith.PeanoNat *)
  
  (* PeanoNat.Nat.Even = fun n : nat => exists m : nat, n = (2 * m)%coq_nat *)
  (*    : nat -> Prop *)

  (* %Coq.Arith.Even *)
  
  (* Inductive even : nat -> Prop := *)
  (* | even_O : even 0 *)
  (* | even_S : forall n, odd n -> even (S n) *)
  (* with odd : nat -> Prop := *)
  (* odd_S : forall n, even n -> odd (S n). *)

  (* Lemma even_equiv : forall n : nat, even n <-> PeanoNat.Nat.Even n. *)
  (* Lemma odd_equiv : forall n : nat, odd n <-> PeanoNat.Nat.Odd n. *)
  (* Lemma even_or_odd : forall n : nat, even n \/ odd n. *)

End nat2.

Section Three_Color_Triangle_Problem_nec.

  Lemma caseN :
    forall n : nat, (exists k : nat, ( n = 0 \/ (3 .^ k <= n /\ n <= 2 * 3 .^ k) \/ (2 * 3 .^ k + 1 <= n /\ n < 3 .^ k.+1))).
  Proof.
    elim=> [ | n IHn].
    - exists 0.
      by left. 
    - destruct IHn as [m].
      move: H => IHm.
      case IHm => IHm'.
      exists 0; rewrite IHm'.
      right; left.
      by split. 
      
      have Case1 : n.+1 = 1 \/ n.+1 >= 2.
      by apply (case1 n).  

      case Case1 => Case1'.
      + exists 0.
        right; left.
        rewrite Case1'.
        by rewrite /=.

      + have Case3m1 : (n.+1 < 3 .^ m.+1) \/ (n.+1 = 3 .^ (m.+1)).
        apply case3m1.
        case IHm' => Range.
        destruct Range as [Range1 Range2].
        by apply leq23m_3m1.
        by destruct Range as [Range1 Range2].

        case Case3m1 => Case3m1'.
        * exists m.
          move: IHm'; rewrite connect; move=> IHm'.
          rewrite connect.
          destruct IHm' as [IHm'_left IHm'_right].
          right.
          split.
          by apply leqn_n1.
          by []. 
        * exists (m.+1).
          move: IHm'; rewrite connect; move=> IHm'.
          rewrite connect.
          destruct IHm' as [IHm'_left IHm'_right].
          right.
          rewrite Case3m1'.
          split.
          by [].
          by apply leq3m_3m1.
  Qed.    
               
  (* Lemma caseN' : *)
  (*   forall (n : nat), ( even n \/ ( odd n /\ exists k : nat, (3 .^ k <= n <= 2 * 3 .^ k) \/ (2 * 3 .^ k + 1 <= n < 3 .^ k.+1))). *)  

  Lemma Paint_Alternate :
    forall y : nat,
      ((forall (x1 : nat), (exists k1, x1 = 2 * k1) -> Cpos x1 y blu) /\ (forall (x2 : nat), (exists k2, x2 = 2 * k2 + 1) -> Cpos x2 y yel)) ->
      (forall (x : nat), Cpos x (y + 1) red).
  Proof.
    move=> y Paint x; destruct Paint as [Paint_Even Paint_Odd].
    Locate even_or_odd.
    case (even_or_odd x).
    + rewrite  even_equiv.
      rewrite /Nat.Even.
      move=> H; destruct H as [m].
      * have Blue : Cpos x y blu.
        apply Paint_Even.
        by exists m.     
      * have Yellow : Cpos (x + 1) y yel.
        apply Paint_Odd.
        exists m.
        by apply addmp.
      * have Red : exists c : Color, Cpos x (y + 1) c.
        by apply C_exists.
        destruct Red as [c].
      * have Mix : c = mix blu yel.
        apply (C_mix x y).
        by split.
        rewrite /= in Mix; by rewrite Mix in H0.
    + rewrite  odd_equiv.
      rewrite /Nat.Odd.
      move=> H; destruct H as [m].
      * have Yellow : Cpos x y yel.
        apply Paint_Odd.
        by exists m.     
      * have Blue : Cpos (x + 1) y blu.
        apply Paint_Even.
        exists (m + 1).
        rewrite mulnDr.
        rewrite muln1.
        rewrite H.
      * have elim_plus : ((2 * m)%coq_nat + 1)%coq_nat = (2 * m)%coq_nat + 1.
        by [].
        rewrite elim_plus. rewrite- addnA add11.
        by [].
      * have Red : exists c : Color, Cpos x (y + 1) c.
        by apply C_exists.
        destruct Red as [c].  
      * have Mix : c = mix yel blu.
        apply (C_mix x y).
        by split.
        rewrite /= in Mix; by rewrite Mix in H0.
  Qed.

  Lemma Red_Y1 :
    forall (y : nat),
      (forall (x1 :nat), Cpos x1 y red) -> (forall (x2 :nat), Cpos x2 (y + 1) red).
  Proof.
    move=> y Paint x2.
    - have Red1 : Cpos x2 y red.
      by apply Paint.
    - have Red2 : Cpos (x2 + 1) y red.
      by apply Paint.
    - have Red' : exists c : Color, Cpos x2 (y + 1) c.
      by apply C_exists.
      destruct Red' as [c' C']. 
    - have Mix : c' = mix red red.
      apply (C_mix x2 y).
      by split.
    - rewrite /= in Mix; by rewrite Mix in C'.
  Qed.
  
  Lemma Red_N :
    forall (n y : nat),
      (forall (x1 :nat), Cpos x1 y red) -> (forall (x2 :nat), Cpos x2 (y + n) red).
  Proof.
    elim=> [ | n IHn].
    - move=> y Paint x2; rewrite addn0.
      by apply Paint.
    - move=> y Paint x2; rewrite- addn1.
      rewrite addnA.
      apply Red_Y1; move=> x1.
      apply IHn.
      move=> x0.
      + have Red1 : Cpos x0 y red.
        by apply Paint.
      + have Red2 : Cpos (x0 + 1) y red.
        by apply Paint.
      + have Red' : exists c : Color, Cpos x0 (y + 1) c.
        by apply C_exists.
        destruct Red' as [c' C']. 
      + have Mix : c' = mix red red.
        apply (C_mix x0 y).
        by split.
      + rewrite /= in Mix; by rewrite Mix in C'.        
  Qed.

  Lemma Red_N' :
    forall (y n : nat),
      (forall (x1 :nat), Cpos x1 y red) -> (forall (x2 :nat), Cpos x2 (y + n) red).
  Proof.
    move=> n y; by apply Red_N.
  Qed.
      
  Lemma Three_Color_Triangle_Problem_nec_even :
    forall n x y: nat,
      (1 <= n) ->
      (exists k, n = 2 * k) ->
      ((forall (x1 : nat), (exists k1, x1 = 2 * k1) -> Cpos x1 y blu) /\
      (forall (x2 : nat), (exists k2, x2 = 2 * k2 + 1) -> Cpos x2 y yel)) ->
      ( ~ (exists k :nat, n = 3 .^ k) -> ~ forall (c0 c1 c2 : Color),((Cpos x y c0 /\ Cpos (x + n) y c1 /\ Cpos x (y + n) c2) -> c2 = mix c0 c1)).
  
  Proof.
    (* move=> n; case n. *)
    (* - by move=> x y c0 c1 c2 Even.  *)
    move=> n x y.
    move=> NotZero_N Even_N Paint Not3k Triangle.
    destruct Even_N as [m]; move: H => Even_N.
    have Alternate :
      ((forall (x1 : nat), (exists k1, x1 = 2 * k1) -> Cpos x1 y blu) /\ (forall (x2 : nat), (exists k2, x2 = 2 * k2 + 1) -> Cpos x2 y yel)) ->
      (forall (x : nat), Cpos x (y + 1) red).
    by apply Paint_Alternate.
    specialize (Alternate Paint).
    destruct Paint as [Paint_Even Paint_Odd].
    - have Red_Y1 :
        (forall x1 : nat, Cpos x1 y red) -> forall (x2 : nat), Cpos x2 (y + 1) red.
      by apply Red_N.
    - have Red_YN :
        (forall x1 : nat, Cpos x1 (y + 1) red) -> forall (x2 : nat), Cpos x2 (y + n) red.
      move=> Paint_Red_Y1.
      apply Red_N.
    - have Red_Y1N :
        (forall x1 : nat, Cpos x1 (y + 1) red) -> forall (x2 : nat), Cpos x2 (y + 1 + n) red.
      by apply Red_N.
      (* specialize(Red_Y1N Alternate). *)
      (* + have N' : exists n' : nat, n = n' + 1. *)
      (*   exists ((2 * m) - 1). *)
      (*   rewrite- Even_N. *)
        * have NotZero_M : m <> 0.
          move=> mZero.
          rewrite mZero in Even_N.
          rewrite muln0 in Even_N.
          rewrite Even_N in NotZero_N.
          by [].
        * have notZero_N : n <> 0.
          move=> Zero_N.
          rewrite Zero_N in Even_N.
        * have Zero_M : m = 0.
          * have tmp : Nat.div2 (2 * m) = m.
            by apply Nat.div2_double.
          rewrite- Even_N in tmp.
          by [].
        by [].
    + have N' : exists n' : nat, n = n' + 1.
        exists ((2 * m) - 1).
        rewrite- Even_N.
        rewrite addn1; rewrite subn1.
        symmetry.
      by rewrite  prednK.

      destruct N' as [n' N'].

      
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
  Admitted.
  
  Lemma Three_Color_Triangle_Problem_nec_oddA :
    forall (n x y : nat),
    (exists k:nat, (3 .^ k <= n <= 2 * 3 .^ k)) -> ~ forall c0 c1 c2 : Color, Triangle x y n c0 c1 c2.
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
  
  Lemma LongEvenA:
    forall (k n x y : nat),
      ((3.^k).*2 + 1 <= n < (3.^k).+1) ->
      (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle x1 y1 (3 .^ k) c0 c1 c2) ->
      (forall i: nat,(0 <= i <= n -> Cpos (x+i) y (colorBYB x n k (x+i)))) -> 
      (
        (forall i: nat,(0 <= i <= n - (3.^k).*2 -> Cpos (x+i) (y+3.^k) red))
        /\
        (forall i: nat,(3.^k <= i <= n - 3.^k -> Cpos (x+i) (y+3.^k) red))
      ).
  Proof.
    move=> k n x y.  move /andP. move => [A B] triangle topcolor.
    have exp3Pos: (0 < 3.^k) = true. by apply expn3Pos.    
    apply conj.
    - (* first part *)
      move=> i. move /andP. move => [C D].
      + have E: 0 <= i <= n.
        apply /andP. apply conj. done.
        apply (trans_lelele D), leq_subr.
      + have A1: (3.^k) <= n.
        have A11: ((3.^k) <= (3.^k).*2 + 1).
        rewrite- addnn. rewrite eql_assoc_plus. rewrite- eql_le_plus_l. by apply leq0n. 
          by rewrite (trans_lelele A11 A).
      + have A2: (3 .^ k).*2 <= n. 
        rewrite addn1 in A. by apply ltnW.         
      + have A3: n - (3.^k).*2 <= (3.^k).-1.
        have A31: (0 < 3.^k) = true. by apply expn3Pos.
        rewrite- (ceql_S_le_le_P (n - (3 .^ k).*2) A31). 
        rewrite (ceql_minus_lt_lt_plus_l (3 .^ k) A2).
        apply (trans_ltltlt B).
        rewrite- (addn1 (3 .^ k)).
        rewrite- (eql_comm_plus 1 (3 .^ k)).
        rewrite- eql_mono_plus_lt_plus.
        have X: 2 = 1.*2. done. rewrite {1} X. 
        rewrite leq_double. by apply expn3Pos. 
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
    - (* second part *)
      move=> i. move /andP. move => [C D].      
      + have E: 0 <= i <= n.
        apply /andP. apply conj. done.
        apply (trans_lelele D), leq_subr.
      + have A1: (3.^k) <= n.
        have A11: ((3.^k) <= (3.^k).*2 + 1).
        rewrite- addnn. rewrite eql_assoc_plus. rewrite- eql_le_plus_l. by apply leq0n. 
        by rewrite (trans_lelele A11 A).
      + have A2: (3 .^ k).*2 <= n. 
        rewrite addn1 in A. by apply ltnW.         
      + have A3: n - (3.^k).*2 <= (3.^k).-1.        
        rewrite- (ceql_S_le_le_P (n - (3 .^ k).*2) exp3Pos). 
        rewrite (ceql_minus_lt_lt_plus_l (3 .^ k) A2).
        apply (trans_ltltlt B).
        rewrite- (addn1 (3 .^ k)).
        rewrite- (eql_comm_plus 1 (3 .^ k)).
        rewrite- eql_mono_plus_lt_plus.
        have X: 2 = 1.*2. done. rewrite {1} X. 
        rewrite leq_double. by apply expn3Pos.
      + have A4: 3.^k <= i <= n-(3.^k).
        apply/andP. apply conj. done. done. 
      + have CposY: Cpos (x+i) y yel. 
        ++ have colY: colorBYB x n k (x+i) = yel. apply (lemBYB2 x y n k i A4).
        ++ rewrite- colY. by apply C_paint. 
      + have CposB: Cpos (x+(3.^k)+i) y blu.
        ++ have A5: (n-(3.^k)).+1 <= (3.^k)+i <= n.
           apply /andP. apply conj.
           rewrite (ceql_minus_lt_lt_plus_r (3.^k+i) A1).
           apply (trans_ltlelt B). rewrite eql_assoc_plus. 
           rewrite- (eql_lt_plus_l (3.^k) (i + 3 .^ k)).
           apply (trans_ltlelt exp3Pos). rewrite- eql_le_plus_r. done. by rewrite (ceql_plus_le_le_minus_r i A1).
        ++ have colB: colorBYB x n k (x+(3.^k)+i) = blu.
           rewrite eql_assoc_plus. by apply (lemBYB3 x y n k ((3.^k)+i)).            
        ++ rewrite- colB. by apply C_paint.            
      + have CposR: Cpos (x+i) (y+(3.^k)) red.
        have mixR: red = mix yel blu. done. 
        rewrite mixR.
        apply Bottom_color_of_triangle. done. done. 
        rewrite eql_assoc_plus. rewrite (eql_comm_plus i (3.^k)). rewrite- eql_assoc_plus. done.
        done.
  Qed.
  
  Lemma LongEvenB:
    forall (k n x y : nat),
      ((3.^k).*2 + 1 <= n < (3.^k).+1) ->
      (forall(x1 y1:nat), forall(c0 c1 c2: Color), Triangle x1 y1 (3 .^ k) c0 c1 c2) ->
      (forall i: nat,(0 <= i <= n -> Cpos (x+i) y (colorBYB x n k (x+i)))) ->
      forall i:nat, (0 <= i <= n-(3.^k).*2) -> Cpos (x+i) (y+(3.^k).*2) red. 
  Proof.
    move=> k n x y rangeN triangle color i rangeI. 

  Qed.
  
  
  
  
  Lemma Three_Color_Triangle_Problem_nec_oddB :
    forall (n x y : nat), 
      (exists m: nat, n = 2*m) -> 
      (exists k:nat, (2 * 3 .^ k + 1 <= n /\ n < 3 .^ k.+1)) -> ~ forall c0 c1 c2 : Color, Triangle x y n c0 c1 c2.
  Proof.
    move=> n x y [m even] [k [nLB nUB]] Triangle.
    rewrite /Triangle in Triangle.
    assert 
    

forall n : nat, (exists k : nat, ( n = 0 \/  \/ )).
    
  Admitted.







  
  Lemma Three_Color_Triangle_Problem_nec' :
    forall (n x y : nat) (c0 c1 c2 : Color),
      ~ (exists k :nat, n = 3 .^ k) -> ~ ((Cpos x y c0 /\ Cpos (x + n) y c1 /\ Cpos x (y + n) c2)  -> c2 = mix c0 c1).
  Proof.

  Admitted.
    

  Theorem Three_Color_Triangle_Problem_nec :
    forall (n x y : nat) (c0 c1 c2 : Color),
      ((Cpos x y c0 /\ Cpos (x + n) y c1 /\ Cpos x (y + n) c2)  -> c2 = mix c0 c1) -> (exists k :nat, n = 3 .^ k).
  Proof.
    move=> n x y c0 c1 c2.
    apply Contraposition.
    by apply Three_Color_Triangle_Problem_nec'.
  Qed.

End Three_Color_Triangle_Problem_nec.



Section Three_Color_Triangle_Problem.


  
  Theorem Three_Color_Triangle_Problem_sufnec :
    forall (n x y : nat) ,
      (exists k : nat, n = 3 .^ k) <->
      (forall (c0 c1 c2 : Color),(Triangle x y n c0 c1 c2)).
  Proof.
    move=> n x y. split.
    move=> H c0 c1 c2.
    rewrite /Triangle.
    - by apply Three_Color_Triangle_Problem_suf.
    - by apply Three_Color_Triangle_Problem_nec.
  Qed.
  
  Theorem Three_Color_Triangle_Problem :
    forall (n : nat) ,
      (exists k :nat, n = 3 .^ k) <-> (forall (c0 c1 c2 : Color), (Cpos 0 0 c0 /\ Cpos n 0 c1 /\ Cpos 0 n c2) -> c2 = mix c0 c1).
  Proof.
    move=> n c0 c1 c2.
    by apply Three_Color_Triangle_Problem_sufnec.
  Qed.

End Three_Color_Triangle_Problem.
