(* The file presents various lemmas for manipulating arities and spine forms. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma iget_All1 i P C Cs : iget i Cs C -> All1 P Cs -> P C.
Proof.
  elim=>{i C Cs}.
  move=>C Cs tyCs. by inv tyCs.
  move=>i C C' Cs ig ih tyCs.
  inv tyCs.
  eauto.
Qed.

Inductive arity_spine :
  context term -> term -> sort -> list term -> term -> sort -> Prop :=
| arity_spine_nil Γ A s l :
  Γ |> U ->
  Γ ⊢ A : s @ l : U ->
  arity_spine Γ A s nil A s
| arity_spine_pi Γ1 Γ2 Γ hd tl A B B' s r t u l :
  Γ1 |> s ->
  [Γ1] ⊢ Pi A B s r t : t @ l : U ->
  Γ1 ⊢ hd : A : s ->
  Γ1 ∘ Γ2 => Γ ->
  arity_spine Γ2 B.[hd/] r tl B' u ->
  arity_spine Γ (Pi A B s r t) t (hd :: tl) B' u.

Lemma app_arity_spine Γ1 Γ2 Γ m ms A B s t :
  Γ1 ⊢ m : A : s ->
  arity_spine Γ2 A s ms B t ->
  Γ1 ∘ Γ2 => Γ ->
  Γ ⊢ spine m ms : B : t.
Proof.
  move=>tym tsp. elim: tsp Γ1 Γ m tym=>//={Γ2 ms A B s t}.
  move=>Γ2 A s l k tyA Γ1 Γ m tym mrg.
  { have->//:=merge_pureR mrg k. }
  move=>Γ1 Γ2 Γ hd tl A B B' s r t u l k tyP tyhd mrg ar ih Γ0 Γ3 m tym mrg0.
  { have[G[mrg1 mrg2]]:=merge_splitL (merge_sym mrg0) mrg.
    apply: ih; eauto.
    apply: clc_app.
    apply: k.
    apply: merge_sym; eauto.
    apply: tym.
    apply: tyhd. }
Qed.

Lemma arity_rearity_ok Γ A B I k s r t u l1 l2 :
  Γ ⊢ A : B : u -> B <: s @ l1 -> arity r l2 A -> Γ ⊢ I : A : u -> r ≤ k ->
  Γ ⊢ rearity k t I A : U @ l1 : U.
Proof.
  move=> ty. elim:ty k s r t l1 l2 I=>{Γ A B u}.
  all: try solve[intros;
    match goal with
    | [ H : arity _ _ _ |- _ ] => inv H
    end].
  move=>Γ s l key k s0 r t l1 l2 I sb ar tyI leq.
  { inv ar.
    have[_ lt]:=sub_sort_inv sb.
    have sb1 : U @ l <: U @ l1.
    apply: sub_sort; eauto.
    have {sb}sb2 : U @ l.+1 <: U @ l1.
    apply: sub_sort; eauto.
    destruct k.
    apply: clc_pi.
    apply: key.
    inv leq.
    apply: clc_conv.
    apply: sb1.
    eauto.
    apply: clc_axiom.
    apply: re_pure.
    apply: clc_conv.
    apply: sb2.
    apply: clc_axiom.
    apply: re_pure.
    apply: clc_axiom.
    apply: re_pure.
    apply: clc_conv.
    apply: sb2.
    apply: clc_axiom.
    eauto.
    apply: clc_axiom.
    apply: re_pure. }
  move=>Γ A B s r t i key tyA ihA tyB ihB k s0 r0 t0 l1 l2 I sb ar tyI leq.
  { inv ar=>//=.
    have ty0 : A :U Γ ⊢ Var 0 : A.[ren (+1)] : U.
    { apply: clc_var.
      constructor; eauto. }
    have tyIw : A :U Γ ⊢ I.[ren (+1)] : (Pi A B U U U).[ren (+1)] : U.
    { apply: eweakeningU; eauto. }
    have p : A :U Γ |> U.
    { constructor; eauto. }
    have mrg : A :U Γ ∘ A :U Γ => A :U [Γ].
    { constructor.
      rewrite<-pure_re; eauto.
      apply: merge_pure; eauto. }
    have ty:=clc_app p mrg tyIw ty0.
    asimpl in ty.
    have{}ty:=ihB _ _ _ t0 _ _ _ sb H0 ty leq.
    have[_ lt]:=sub_sort_inv sb.
    have {}sb: U @ i <: U @ l1.
    { apply: sub_sort.
      eauto. }
    apply: clc_pi; eauto.
    apply: clc_conv; eauto.
    apply: clc_axiom.
    apply: re_pure. }
  move=>Γ A B m s i sb tym ihm tyB _ k s0 r t l1 l2 I sb' ar tyI leq.
  { apply: ihm; eauto.
    apply: sub_trans; eauto. }
Qed.

Definition kpi k A B s r t :=
  match k with
  | U => Pi A B s r t
  | L => B
  end.

Lemma rearity_spine Γ ms I A k s r t u v l1 l2 :
  arity_spine Γ A u ms (s @ l1) v ->
  arity r l2 A ->
  r ≤ k ->
  Γ |> U ->
  Γ ⊢ I : A : U ->
  arity_spine Γ (rearity k t I A) U ms (kpi k (spine I ms) (t @ l1) U U U) U.
Proof.
  move e:(s @ l1)=>n tsp.
  elim: tsp I k s r t l1 l2 e=>//={Γ ms A u v n}.
  move=>Γ A s l key tyA I k s0 r t l1 l2 e ar leq _ tyI; subst.
  { inv ar.
    destruct k=>//=.
    inv leq.
    have sb: U @ l1 <: U @ l1.+1.
    { apply: sub_sort; eauto. }
    apply: arity_spine_nil; eauto.
    apply: clc_pi.
    eauto.
    apply: clc_conv.
    apply: sb.
    eauto.
    apply: clc_axiom.
    apply: re_pure.
    apply: clc_axiom.
    apply: re_pure.
    apply: arity_spine_nil; eauto.
    apply: clc_axiom.
    eauto. }
  move=>Γ1 Γ2 Γ hd tl A B B' s r t u l key1 tyP tyhd mrg tsp ih
    I k s0 r0 t0 l1 l2 e ar leq key tyI; subst.
  { inv ar.
    have[_ key2]:=merge_pure_inv mrg key.
    have e1:=merge_pureL mrg key1.
    have e2:=merge_pureR mrg key2.
    subst.
    pose proof(arity_subst (hd .: ids) H0) as ar'.
    have ty0:=clc_app key mrg tyI tyhd.
    have {}ih:=ih _ _ _ _ t0 _ _ erefl ar' leq key ty0.
    have ty1 : A :U Γ1 ⊢ Var 0 : A.[ren (+1)] : U.
    { apply: clc_var.
      constructor; eauto. }
    have tyIw : A :U Γ1 ⊢ I.[ren (+1)] : (Pi A B U U U).[ren (+1)] : U.
    { apply: eweakeningU; eauto. }
    have mrg1 : A :U Γ1 ∘ A :U Γ1 => A :U [Γ1].
    { rewrite<-pure_re; eauto.
      constructor; eauto. }
    have ty2:=clc_app (key_u A key) mrg1 tyIw ty1.
    asimpl in ty2.
    have[l0[tyA[sb[_ tyB]]]]:=pi_inv tyP.
    have tyr:=arity_rearity_ok t0 tyB sb H0 ty2 leq.
    apply: arity_spine_pi; eauto.
    apply: clc_pi.
    apply: re_pure.
    apply: clc_conv.
    apply: sb.
    eauto.
    apply: clc_axiom.
    apply: re_pure.
    simpl. rewrite<-re_invo=>//.
    erewrite rearity_subst; eauto.
    asimpl; eauto. }
Qed.

Ltac solve_Ind_spine' :=
  match goal with
  | [ H : spine' (Ind _ _ _) ?ms = _ |- _ ] =>
    induction ms; simpl; intros; discriminate
  | [ H : _ = spine' (Ind _ _ _) ?ms  |- _ ] =>
    induction ms; simpl; intros; discriminate
  end.

Lemma arity_spine_pi_rcons Γ1 Γ2 Γ A B C n ms s r t u v :
  arity_spine Γ1 A u ms (Pi B C s r t) v ->
  Γ2 |> s ->
  Γ2 ⊢ n : B : s ->
  Γ1 ∘ Γ2 => Γ ->
  arity_spine Γ A u (rcons ms n) C.[n/] r.
Proof.
  move e:(Pi B C s r t)=>T sp.
  elim: sp Γ2 Γ B C s r t n e=>{Γ1 A u ms T v}.
  move=>Γ1 A s l k1 tyA Γ2 Γ B C s0 r t n e k2 tyn mrg; subst.
  { rewrite/rcons.
    have[l0[tyB[sb[_ tyC]]]]:=pi_inv tyA.
    have[e lt]:=sub_sort_inv sb; subst.
    have[e _]:=merge_re_re mrg.
    have {}tyC : Γ1 ⊢ C.[n/] : r @ l0 : U.
    { destruct s0.
      have//=:=substitution tyC k2 mrg tyn.
      have->//:=merge_pureR mrg k2.
      have//:=substitutionN tyC tyn. }
    apply: arity_spine_pi.
    apply: k2.
    rewrite<-e.
    rewrite<-pure_re; eauto.
    eauto.
    apply: merge_sym; eauto.
    apply: arity_spine_nil; eauto. }
  move=>Γ1 Γ2 Γ hd tl A B B' s r t u l k1 tyP tyhd mrg1 ar
    ih Γ0 Γ3 B0 C s0 r0 t0 n e k2 tyn mrg2; subst.
  { have[G[mrg3 mrg4]]:=merge_splitR mrg2 mrg1.
    apply: arity_spine_pi.
    apply: k1.
    apply: tyP.
    apply: tyhd.
    apply: mrg4.
    apply: ih; eauto. }
Qed.

Lemma ind_spine'_invX Γ A B Cs ms s t l :
  Γ |> U ->
  arity s l A ->
  Γ ⊢ spine' (Ind A Cs s) ms : B : t ->
  exists A' t l',
    arity s l A' /\
    Γ ⊢ A' : t @ l' : U /\
    arity_spine Γ A U (rev ms) A' t /\
    A' <: B.
Proof.
  move e:(spine' (Ind A Cs s) ms)=>n k a ty.
  elim: ty A Cs ms s l a e k=>{Γ B t n}.
  all: try solve[intros; exfalso; solve_Ind_spine'].
  move=>Γ1 Γ2 Γ A B m n s r t _ mrg tym ihm tyn ihn A0 Cs ms s0 l ar sp k.
  { move: sp. destruct ms.
    rewrite/rev/catrev=>//=.
    move=>//=e. inv e.
    have[k1 k2]:=merge_pure_inv mrg k.
    have e1:=merge_pureL mrg k1.
    have e2:=merge_pureR mrg k2.
    subst.
    have[A'[t0[l0[ar'[tyA'[sp sb]]]]]]:=ihm _ _ _ _ _ ar erefl k.
    inv ar'.
    exfalso; solve_sub.
    move: sb=>/sub_pi_inv[eA[sB[e1[e2 e3]]]]; subst.
    move: tyA'=>/pi_inv[l3[tyA1[sb[_ tyB0]]]].
    exists B0.[n/]. exists U. exists l3.
    have {}tyn : Γ1 ⊢ n : A1 : U.
    { apply: clc_conv.
      apply: conv_sub.
      apply: conv_sym.
      apply: eA.
      eauto.
      rewrite<-pure_re; eauto. }
    repeat split; eauto.
    apply: arity_subst; eauto.
    replace (U @ l3) with (U @ l3).[n/] by autosubst.
    apply: substitution.
    apply: tyB0.
    apply: k.
    apply: mrg.
    eauto.
    rewrite rev_cons.
    apply: arity_spine_pi_rcons; eauto.
    apply: sub_subst; eauto. }
  move=>Γ A Cs s l1 l2 k ar cCs tyA ihA tyCs A0 Cs0 ms s0 l0 ar0 sp _.
  { move: sp. destruct ms.
    rewrite/rev/catrev=>//=.
    move=>[e1 e2 e3]; subst.
    exists A. exists U. exists l2.
    repeat split; eauto.
    apply: arity_spine_nil; eauto.
    move=>//=e. }
  move=>Γ A B m s i sb tym ihm tyB _ A0 Cs ms s0 l0 ar sp k; subst.
  { have{ihm}[A'[t[l[ar'[tyA'[sp sb']]]]]]:=ihm _ _ _ _ _ ar erefl k.
    exists A'. exists t. exists l.
    repeat split; eauto.
    apply: sub_trans; eauto. }
Qed.

Lemma ind_spine_invX Γ A B Cs ms s l t :
  Γ |> U ->
  arity s l A ->
  Γ ⊢ spine (Ind A Cs s) ms : B : t ->
  exists A' t l0,
    arity s l A' /\
    Γ ⊢ A' : t @ l0 : U /\
    arity_spine Γ A U ms A' t /\
    A' <: B.
Proof.
  rewrite spine_spine'_rev.
  move=>k a ty.
  move/ind_spine'_invX in ty; eauto.
  rewrite revK in ty; eauto.
Qed.

Lemma ind_spine_inv Γ A Cs ms s t l1 l2 :
  Γ |> U ->
  arity s l1 A ->
  Γ ⊢ spine (Ind A Cs s) ms : t @ l2 : U ->
  arity_spine Γ A U ms (t @ l1) U /\ s = t.
Proof.
  move=>k ar ty.
  have[A'[t0[l0[ar'[tyA'[sp sb]]]]]]:=ind_spine_invX k ar ty.
  inv ar'.
  have[e _]:=sub_sort_inv sb; subst.
  have[sb' _]:=sort_inv tyA'.
  have[e lt]:=sub_sort_inv sb'; subst.
  eauto.
  exfalso; solve_sub.
Qed.

Lemma ind_spine' Γ A B Cs s t ms :
  Γ |> U ->
  Γ ⊢ spine' (Ind A Cs s) ms : B : t ->
  Γ ⊢ Ind A Cs s : A : U.
Proof.
  move e:(spine' (Ind A Cs s) ms)=>n k ty.
  elim: ty A Cs s ms k e=>//{Γ n B t};
  try solve[intros; solve_Ind_spine'].
  move=>Γ1 Γ2 Γ A B m n s r t _ mrg tym ihm tyn ihn A0 Cs s0 ms k e.
  { destruct ms; simpl in e; inv e.
    have[k1 k2]:=merge_pure_inv mrg k.
    have->:=merge_pureR mrg k2.
    eauto. }
  move=>Γ A Cs s l1 l2 k ar cCs tyA ihA tyCs ihCs Cs0 s0 ms _ e.
  { destruct ms; simpl in e; inv e.
    apply: clc_indd; eauto. }
Qed.

Lemma ind_spine Γ A B Cs s t ms :
  Γ |> U ->
  Γ ⊢ spine (Ind A Cs s) ms : B : t ->
  Γ ⊢ Ind A Cs s : A : U.
Proof.
  rewrite spine_spine'_rev.
  apply: ind_spine'.
Qed.
