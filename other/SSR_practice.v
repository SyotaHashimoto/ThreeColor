From mathcomp
     Require Import ssreflect.

Section ModusPonens.
  
  Variables X Y : Prop.
  
  Hypothesis XtoY_is_true : X -> Y.
  Hypothesis X_is_true : X.

  Theorem MP : Y.
  Proof.
    move: X_is_true.
    by [].  
  Qed.
  
End ModusPonens.

(* Scetion [セクション名]. ~ End [セクション名]. のように用いる *)
(* セクション (節) を導入するコマンド *)

(* Parameter (Parameters) ,  Axiom で定義されたものは End 以降で使用可 *)
(* Variable (Variables) ,  Hypothesis (Hypotheses) で定義されたものは End 以降で使用不可 *)
(* 慣習として Axiom , Hypothesis (Hypotheses) は Prop を扱う際には用いる *)

(* by はターミネータとよばれる部類のタクティック *)
(* by の後にタクティックや [] を続けて記述する形で用いる *)
(* 慣習として by の後に続くタクティックで証明が終わる際に用いる *)

Section HilbertSAxiom.
  
  Variables A B C : Prop.
  
  Theorem HS1 : (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
  Proof.
    move=> AtoBtoC_is_true.
    move=> AtoB_is_true.
    move=> A_is_true.

    apply: (MP B C).
    
    apply: (MP A (B -> C)).
    by [].
    by [].

    apply: (MP A B).
    by [].
    by [].                
  Qed.

  Theorem HS2 : (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
  Proof.
    move=> AtoBtoC_is_true AtoB_is_true A_is_true.
    by apply: (MP B C); [apply: (MP A (B -> C)) | apply: (MP A B)].          
  Qed.

  Theorem HS3 : (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
  Proof.
    move=> AtoBtoC_is_true AtoB_is_true A_is_true.
    by move: A_is_true (AtoB_is_true A_is_true).  
  Qed.
  
End HilbertSAxiom.

From mathcomp
     Require Import ssrnat.

(* ssrnat を読み込むと S n が n.+1 に表記が変更される *)

Section naturalnumber.
  
  Lemma add0nEqn (n :nat) : 0 + n = n.
  Proof.
      by [].
  Qed.

  Lemma addn3Eq2n1 (n :nat) : n + 3 = 2 + n + 1.
  Proof.
    rewrite addn1.
    rewrite add2n.
    rewrite addnC.
    by [].
  Qed.

  Fixpoint sum n := if n is m.+1 then sum m + n else 0.

  Lemma sumGauss (n : nat) : sum n * 2 = (n + 1) * n.
  Proof.
    elim: n => [// | n IHn].
    rewrite mulnC.
    rewrite (_ : sum (n.+1) = n.+1 + (sum n)); last first.
    rewrite /=.
    by rewrite addnC.
    rewrite mulnDr.
    rewrite mulnC in IHn.
    rewrite IHn.
    rewrite 2!addn1.
    rewrite [ _ * n]mulnC.
    rewrite -mulnDl.
    by [].
  Qed.

End naturalnumber.

Set Imlicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Logic.

  Lemma contrap : forall A B : Prop, (A -> B) -> (~B -> ~A).
  Proof.
    rewrite /not.
    move=> A0 B0 AtoB notB.
    by move /AtoB.
  Qed.

  Variable A B C : Prop.

  Lemma AndOrDistL : (A /\ C) \/ (B /\ C) <-> (A \/ B) /\ C.
  Proof.
    rewrite /iff.
    apply: conj.
    -case.
     +case=> AisTrue CisTrue.
        by apply: conj; [apply: or_introl | ].
     +case=> BisTrue CisTrue.
        by apply: conj; [apply: or_intror | ].
    -case=> AorBisTrue CisTrue.
     case: AorBisTrue => [AisTrue | BisTrue ].
        +by apply: or_introl.
        +by apply: or_intror.   
  Qed.

  Lemma JDM (T : Type) (P : T -> Prop) : ~(exists (x :T), P x) <-> forall x, ~(P x).
  Proof.
    apply: conj => Hyp.
    -move=> x0 HPx0.
     apply: Hyp.
     by apply: (ex_intro P x0).
    -by case.
  Qed.

  Hypothesis ExMidLaw : forall P : Prop, P \/ ~P.

  Lemma notnotEq (P : Prop) : ~~P -> P.
  Proof.
    move=> HnotnotP.
    -case: (ExMidLaw (~P)).
     +by move /HnotnotP.
     +by case: (ExMidLaw P).
  Qed.

End Logic.

Section tactic_move.

  Lemma move1 : forall P Q : Prop, (P -> Q) -> P -> Q.
  Proof.
    move=> P.
    move=> Q PQisTrue.
    by [].
  Qed.  
    
  (* move=> [変数名1] ... [変数名n]. のように用いる *)
  (* トップに名前をつけて 1 番目から順にコンテキストに追加する SSR タクティック *)
  (* 束縛変数が対象のとき [変数名 (対象)] : [型] が追加される *)
  (* その他が対象のとき [変数名 (対象)] : [言明] が追加される *)

  Lemma move2 : forall P Q : Prop, (P -> Q) -> P -> Q.
  Proof.
    move=> P Q.
    move: P Q.
    
    move=> P'.
    move: P' => P.

    move=> Q' PQisTrue.
    move: Q' PQisTrue => Q PtoQ .
    by [].
  Qed.

  (* move: [変数名1] ... [変数名n]. のように用いる *)
  (* コンテキストを n 番目から順にトップに戻す SSR タクティック *)

  (* move: [変数名1] ... [変数名n] => <変数名1> ... <変数名n>. のように用いる *)
  (* move: [変数名1] ... [変数名n]. を実行し，続けて move=> <変数名1> ... <変数名n>. を実行 *)

End tactic_move.

Section tactic_apply.

  Lemma apply1_1 : forall A B C : Prop, (A /\ B -> C) -> C.
  Proof.
    move=> A B C.
    apply.
  Abort.

  Lemma apply1_2 : forall A B C D : Prop, (A -> B -> C -> D) -> C -> D.
  Proof.
    move=> A B C D.
    apply.
  Abort.

  (* (P -> Q) -> Q の形をしているサブゴールを P に変形する SSR タクティック *)
  (* P を示すことができれば P -> Q によって Q を証明できることに由来 *)

  (* Abort は証明を中止するコマンド *)
  
  Lemma apply2_1 : forall A B C : Prop, ((A -> B) -> C) -> C.
  Proof.
    move=> A B C.
    apply=> a.
  Abort.

  Lemma apply2_2 : forall A B C D : Prop, ((A -> B -> C) -> D) -> D. 
  Proof.
    move=> A B C D.
    apply=> a b.
  Abort.
 
  (* apply=> [変数名1] ... [変数名n]. のように用いる *)
  (* apply. を実行し，続けて move=> [変数名1] ... [変数名n]. を実行 *)
 
  Lemma apply3 : forall A B : Prop, (A -> B) -> B.
  Proof.
    move=> A B AtoB.
    apply: AtoB.
  Abort.
 
  (* apply: [変数名1] ... [変数名n]. のように用いる *)
  (* move: [変数名1] ... [変数名n]. を実行し，続けて apply. を実行 *)

  Lemma apply3 : forall A B C : Prop, ((A -> B) -> C) -> C.
  Proof.
    move=> A B C AtoBtoC.
    apply: AtoBtoC => a.
  Abort.
 
  (* apply: [変数名1] ... [変数名n] => <変数名1> ... <変数名m>. のように用いる *)
  (* move: [変数名1] ... [変数名n]. を実行し，続けて apply. を実行後さらに move=> <変数名1> ... <変数名m> を実行 *)

End tactic_apply.

From mathcomp
     Require Import ssrbool.

Section tactic_case.

  Lemma case1_1 :
    forall B1 B2 B3 : bool, B1 && (B3 || B2) = B1 && B3 || B1 && B2.
  Proof.
    case.
  Abort.

  (* トップが bool 型の束縛変数のとき，2つのサブゴールに分ける SSR タクティック *)
  (* 束縛変数を1つ目のサブゴールのときは true ，2つ目のサブゴールのときは false に置き換える *)

  Lemma case1_2 :
    forall P Q : Prop, P \/ Q -> P \/ Q.
  Proof.
    move=> P Q.
    case.
  Abort.

  (* トップが A \/ B のとき，2つのサブゴールに分ける SSR タクティック *)
  (* A \/ B -> を1つ目のサブゴールのときは A -> ，2つ目のサブゴールのときは B -> に置き換わる *)

  Lemma case1_3 :
    forall P Q : Prop, P /\ Q -> Q /\ P.
  Proof.
    move=> P Q.
    case.
  Abort.

  (* トップが A /\ B のとき，A /\ B -> を A -> B -> に置き換える SSR タクティック *)

  Lemma case1_4 :
    forall P Q : Prop, True -> P -> Q.
  Proof.
    move=> P Q.
    case.
  Abort.

  (* トップが True のとき，True をなくす SSR タクティック *)

  Lemma case1_5 :
    forall P Q : Prop, false -> P -> Q.
  Proof.
    move=> P Q.
    case.
  Abort.

  (* トップが false のとき，そのサブゴールの証明を終了する SSR タクティック *)
  
  Lemma case1_6 (A : Type) (P : Type -> Prop) :
    (exists a : Type, A -> P a) -> ~(forall a, ~P a).
  Proof.
    case.
  Abort.

  (* トップが exists x, P x のとき，exists x, P x -> を forall x, P x -> に置き換える SSR タクティック *)
  
  Lemma case1_7 :
    forall n : nat, n + 1 = 1 + n.
  Proof.
    case.    
  Abort.

  (* トップが nat 型の束縛変数のとき，2つのサブゴールに分ける SSR タクティック *)
  (* n を1つ目のサブゴールのときは 0 ，2つ目のサブゴールのときは n.+1 に置き換わる *)

  Lemma case2 :
    forall P Q : Prop, P \/ Q -> P \/ Q.
  Proof.
    move=> P Q.
    case=> [HP | HQ].    
  Abort.

  (* case=> [<変数名1> | ... | <変数名n>]. のように用いる *)
  (* case によりサブゴールが n 個に分岐したときに， i 番目のサブゴールに対して move=> Ai を実行する SSR タクティック *)

End tactic_case.

Section tactic_elim.

  Lemma elim1 : forall n : nat, n + n = 2 * n.
  Proof.
    elim.
  Abort.

  (* サブゴールが forall n : nat, P n のとき，2つのサブゴールに分ける SSR タクティック *)
  (* forall n : nat, P n を1つ目のサブゴールのを P 0 ，2つ目のサブゴゴールは forall n : nat, P n -> P n.+1 に置き換える *)
  (* 数学的帰納法を用いるときに実行する *)

  Lemma elim1 : forall n : nat, n + n = 2 * n.
  Proof.
    elim.
  Abort.

  (* サブゴールが forall n : nat, P n のとき，2つのサブゴールに分ける SSR タクティック *)
  (* forall n : nat, P n を1つ目のサブゴールのときは P 0 ，2つ目のサブゴールのときは forall n : nat, P n -> P n.+1 に置き換わる *)
  (* 数学的帰納法を用いるときに実行する *)

  Lemma elim2 : forall n : nat, n + n = 2 * n.
  Proof.
    elim=> [| n IHn].
    by [].
  Abort.

  (* サブゴールが forall n : nat, P n のとき，2つのサブゴールに分ける SSR タクティック *)
  (* forall n : nat, P n を1つ目のサブゴールときは P 0 に置き換える *)
  (* 2つ目のサブゴールのときは forall n : nat, P n -> P n.+1 に置き換え，続けて move=> n IHn. を実行する *)

End tactic_elim.

Section tactic_rewrite.

  Lemma rewrite1 : forall a b c : nat , (a + b) + c = c + a.
  Proof.
    move=> a b c.
    rewrite (_ : a = 0).
  Abort.

  (* rewrite (_ : XXX = YYY). のように用いる *)
  (* サブゴールの XXX を YYY に置き換え，XXX = YYY というサブゴールを追加する SSR タクティック *)

  Lemma rewrite2 : true && (true || false).
  Proof.
    by rewrite /=.
  Abort.

  (* 簡単な計算をおこなう SSR タクティック *)

  Lemma rewrite3_1 (a a0 : nat) : (1 + a = 1) -> (1 + a + a + a + a = 1).
  Proof.
    move=> a_cal.
    rewrite 4!a_cal.
    by [].
  Qed.
    
  (* rewrite <数>!<要素名>. のように用いる *)
  (* rewrite <要素名>. を <数> 回繰り返す SSR タクティック *)

  Lemma rewrite3_2 (a a0 : nat) : (1 + a = 1) -> (1 + a + a + a + a = 1).
  Proof.
    move=> a_cal.
    rewrite !a_cal.
    by [].
  Qed.

  (* rewrite !<要素名>. のように用いる *)
  (* rewrite <要素名>. を可能な繰り返す SSR タクティック *)

  Lemma rewrite4_1 (n m : nat) : (n = 0) -> (n + m = n + n).
  Proof.
    move=> n0.
    rewrite {2}n0.
  Abort.

  (* rewrite {<数>}<要素名>. のように用いる *)
  (* rewrite <要素名>. が可能な位置のうち左から <数> 番目の位置だけを実行する SSR タクティック *)

  Lemma rewrite4_2 (n m : nat) : (n = 0) -> (n + m = n + n).
  Proof.
    move=> n0.
    rewrite {-2}n0.
  Abort.

  (* rewrite {-<数>}<要素名>. のように - を <数> に付けると左から <数> 番目以外の位置だけに実行する *)

  Lemma rewrite5_1 (x y : nat) :
    (forall t u : nat , t + u = u + t) -> (x + y = y + x).
  Proof.
    move=> H.
    rewrite [y + _]H.
    by [].
  Qed.

  (* rewrite [<条件>]<要素名>. のように用いる *)
  (* [条件] を満たす位置に対して rewrite <要素名>. を実行する SSR タクティック *)
  (* [条件] に用いられる _ は何かしらの項を表す *)

  Lemma rewrite5_2 : forall a b c : nat , a + b + 2 * (b + c) = 0.
  Proof.
    move=> a b c.
    rewrite [in 2 * _]addnC.
  Abort.

  (* rewrite [in <条件>]<要素名>. のように用いる *)
  (* [条件] に用いられる _ の位置に対して rewrite <要素名>. を実行する SSR タクティック *)
  (* rewrite [in X in 2 * X] でも可 *)

  Lemma rewrite6 : forall A B : Prop , (A -> B) -> (~B -> ~A).
  Proof.
    move=> A B H.
    rewrite /not.
  Abort.

  (* rewrite /<定義名>. のように用いる *)
  (* 定義に基づいて書き換えを実行する *)
  (* ~ は not，<-> は iff の略記であり，定義名は正式な名前を用いる *)

End tactic_rewrite.

Section tactic_view.

  (* 基本の補題 *)
  (* XXX -> YYY とかかれている言明 *)

  (* 解釈補題 *)
  (* 2つの言明が論理的に等価であることを意味する言明 *)
  (* 具体例として XXX <-> YYY が挙げられる *)

  (* リフレクション *)
  (* Prop 型を bool 型を交換すること *)
  (* リフレクションをする際に用いる補題をリフレクション補題という *)

  Lemma view_move1 (P Q R : Prop) : (P -> Q) -> (P -> R).
  Proof.
    move=> PtoQ.
    move /PtoQ.
  Abort.

  (* move /<基本の補題名>. のように用いる *)
  (* サブゴールのトップを <基本の補題> の必要条件に置き換える SSR タクティック *)

  Lemma view_move2 (P Q : nat -> Prop) :
    (forall n : nat , P n <-> Q n) -> (~Q 0 -> ~P 0).
  Proof.
    move=> PiffQ.
    move /PiffQ.
  Abort.

  (* move /<解釈補題名>. のように用いる *)
  (* サブゴールの仮定のトップを <解釈補題名> の同値な条件に置き換える SSR タクティック *)
  (* move / は基本的に仮定のトップの変形に用いる *)

  Lemma view_move3 (P Q : bool) : P && Q -> Q.
  Proof.
    move /andP.
  Abort.
 
  (* move /<リフレクション補題名>. のように用いる *)
  (* サブゴールの仮定のトップを <解釈補題名> の同値な条件に置き換える SSR タクティック *)

  Lemma view_apply1 (A B C : Prop) : (A -> B) -> (B -> C) -> C.
  Proof.
    move=> AtoB BtoC.
    apply /BtoC /AtoB.
  Abort.

  (* apply /<基本の補題名1> /<基本の補題名2> ... . のように用いる *)
  (* apply <基本の補題名1>. apply <基本の補題名2>. ... を続けて実行する SSR タクティック *)

  Lemma view_apply2 (P Q : nat -> Prop) :
    (forall n : nat, P n <-> Q n) -> Q 0.
  Proof.
    move=> PQ.
    apply /PQ.
  Abort.

  (* apply /<解釈補題名>. のように用いる *)
  (* サブゴール全体を <解釈補題名> の同値な条件に置き換える SSR タクティック *)

  Lemma view_move3 (P Q : bool) : P && Q.
  Proof.
    apply /andP.
  Abort.
 
  (* move /<リフレクション補題名>. のように用いる *)
  (* サブゴール全体を <リフレクション補題名> の同値な条件に置き換える SSR タクティック *)

  Lemma view_case1 (P Q : Prop) : ~P -> (P -> Q).
  Proof.
    move=> H.
    case /H.
  Qed.

  (* case /<基本の補題名>. のように用いる *)
  (* move/ <基本の補題名>. を実行し，続けて case. を実行する SSR タクティック *)

  Lemma view_case2 (A B C D : Prop) : (A <-> B \/ C) -> A -> D.
  Proof.
    move=> Hyp.
    case /Hyp.
  Abort.

  (* case /<解釈補題名>. のように用いる *)
  (* move/ <解釈補題名>. を実行し，続けて case. を実行する SSR タクティック *)

  Lemma view_case3 (P Q : bool) : P || Q -> P || Q.
  Proof.
    case /orP.
  Abort.

  (* case /<リフレクション補題名>. のように用いる *)
  (* move/ <リフレクション補題名>. を実行し，続けて case. を実行する SSR タクティック *)

End tactic_view.  
