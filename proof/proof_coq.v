From mathcomp
     Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
Require Import Classical_Prop.
Require Import PeanoNat Le Lt Plus Mult Even.
Require Import Lia.
Require Import CoqNat.


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

  Fixpoint mix (c0 c1 : Color) : Color :=
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

  Axiom C_conf :
    forall x y : nat, forall c0 c1 c2 : Color, Cconf c0 c1 c2 <-> (c0 = c1 /\ c1 = c2 /\ c2 = c0) \/ (c0 <> c1 /\ c1 <> c2 /\ c2 <> c0).
  (* c0 c1 c2 : Color が3色互いに 同じ色 または 異なる色 である *)

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
    move=> n x y.
    move=> NotZero_N Even_N Paint Not3k Triangle.
    destruct Even_N as [m]; move: H => Even_N.

    (* Cpos x (y + n) red を示す *)
    have Alternate :
      ((forall (x1 : nat), (exists k1, x1 = 2 * k1) -> Cpos x1 y blu) /\ (forall (x2 : nat), (exists k2, x2 = 2 * k2 + 1) -> Cpos x2 y yel)) ->
      (forall (x : nat), Cpos x (y + 1) red).
      by apply Paint_Alternate.
    specialize (Alternate Paint).
    destruct Paint as [Paint_Even Paint_Odd].
    have Red_YN : Cpos x ((y + 1) + (n - 1)) red.
      by apply Red_N.  
    have Rerite_YN : y + 1 + (n - 1) = y + n.
    rewrite- addnA.
    rewrite [1+(n-1)]addnC.
    rewrite subn1.
    rewrite addn1.
    + have prednk : n.-1.+1 = n.
      by apply prednK.
    by rewrite prednk.
    move: Red_YN; rewrite Rerite_YN; move=> Red_YN.

    (* x を even, odd で場合分け開始 *)
    case (even_or_odd x).
    (* x:even の場合開始 *)
    - rewrite even_equiv; rewrite /Nat.Even.
      move=> Even_X.
      destruct Even_X as [m' Even_X].
      rewrite- coqnat_mult in Even_X.

      (* even x と n = 2 * m' より even( x + n ) を示す *)
      have Even_XN : even(x + n).
      apply even_even_plus.
      rewrite even_equiv; rewrite /Nat.Even.
      by exists m'.
      rewrite even_equiv; rewrite /Nat.Even.
      exists m.
      by rewrite- coqnat_mult.

      (* Cpos x y blu を示す *)
      have Blue_Y : Cpos x y blu.
      apply Paint_Even.
      by exists m'.

      (* Cpos (x + n) y blue を示す *)
      have Blue_Y' : Cpos (x + n) y blu.
      apply Paint_Even.
      move: Even_XN.
      rewrite even_equiv; rewrite /Nat.Even.
      move=> Even_XN.
      destruct Even_XN as [k Even_XN].
      rewrite- coqnat_mult in Even_XN.
      by exists k.

      (* Triangle から Cpos x (y + n) blu を示す *)
      have Blue_YN : exists c : Color, Cpos x (y + n) c.
      by apply C_exists.
      destruct Blue_YN as [c' Blue_YN].
      have Mix : c' = mix blu blu.
      apply Triangle.
      by split.
      rewrite /= in Mix; rewrite Mix in Blue_YN.
        
      (* Cpos x (y + n) blu と Cpos x (y + n) red から矛盾を示す *)
      by apply (falseColor x (y + n) red blu).      
      (* (x : even の場合終了) *)

    (* x:odd の場合開始 *)
    (* odd x と Paint_Odd より Cpos x y yel を示す *)
    - rewrite odd_equiv; rewrite /Nat.Odd.
      move=> Odd_X.
      destruct Odd_X as [m' Odd_X].
      rewrite- coqnat_mult in Odd_X; rewrite- coqnat_plus in Odd_X.
      have Yellow_Y : Cpos x y yel.
      apply Paint_Odd.
      by exists m'.
      
      (* odd x と n = 2 * m より odd(x + n) を示す *)
      have Odd_XN : odd(x + n).
      apply odd_plus_l.
      + rewrite odd_equiv; rewrite /Nat.Odd.
        exists m'.
        rewrite- coqnat_plus.
        by rewrite- coqnat_mult.
      + rewrite even_equiv; rewrite /Nat.Even.
        by exists m.
      (* Cpos (x + n) y yel を示す *)
      have Yellow_Y' : Cpos (x + n) y yel.
      apply Paint_Odd.
      move: Odd_XN.
      rewrite odd_equiv; rewrite /Nat.Odd.
      move=> Odd_XN.
      destruct Odd_XN as [m'' Odd_XN].
      by exists m''.
                  
      (* Triangle より Cpos x (y+n) yel を示す *)
      have Yellow_YN : exists c : Color, Cpos x (y + n) c.
      by apply C_exists.
      destruct Yellow_YN as [c' Yellow_YN].
      have Mix : c' = mix yel yel.
      apply Triangle.
      by split.
      rewrite /= in Mix; rewrite Mix in Yellow_YN.
      
      (* これと Cpos x (y+n) red より矛盾を示す *)
      by apply (falseColor x (y + n) red yel). 
      (* (x : odd の場合終了) *)
  Qed.
  
  Lemma Three_Color_Triangle_Problem_nec_oddA :
    forall (n x y : nat) (c0 c1 c2 : Color),
      ~ (exists k :nat, n = 3 .^ k) -> ~ ((Cpos x y c0 /\ Cpos (x + n) y c1 /\ Cpos x (y + n) c2)  -> c2 = mix c0 c1).
  Proof.
    
  Admitted.

  Lemma Three_Color_Triangle_Problem_nec_oddB :
    forall (n x y : nat) (c0 c1 c2 : Color),
      ~ (exists k :nat, n = 3 .^ k) -> ~ ((Cpos x y c0 /\ Cpos (x + n) y c1 /\ Cpos x (y + n) c2)  -> c2 = mix c0 c1).
  Proof.
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
