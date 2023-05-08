From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sort_inv Γ C s t l :
  Γ ⊢ s @ l : C : t -> U @ l.+1 <: C /\ t = U.
Proof.
  move e:(s @ l)=>m tp.
  elim: tp s l e=>//={Γ m C t}.
  move=>Γ s l k s0 l0[e1 e2]; subst.
  eauto.
  move=>Γ A B m s i sb tym ihm tyB _ s0 l e; subst.
  have[sb' e]:=ihm _ _ erefl; subst.
  split; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma pi_inv Γ A B C s r t1 t2 :
  Γ ⊢ Pi A B s r t1 : C : t2 ->
  exists l,
    Γ ⊢ A : s @ l : U /\ t1 @ l <: C /\ t2 = U /\
    match s with U => A :U Γ | L => _: Γ end ⊢ B : r @ l : U.
Proof with eauto using key.
  move e:(Pi A B s r t1)=>m tp.
  elim: tp A B s r t1 e=>//{Γ C m t2}.
  move=>Γ A B s r t i k tyA ihA tyB ihB A0 B0 s0 r0 t1
    [e1 e2 e3 e4 e5]; subst.
  exists i.
  repeat split; eauto.
  destruct s.
  simpl in tyB. rewrite<-pure_re in tyB...
  simpl in tyB. rewrite<-pure_re in tyB...
  move=>Γ A B m s i sb tym ihm tyB _ A0 B0 s0 r t1 e; subst.
  have{ihm}[l[tyA[sb'[e tyB0]]]]:=ihm _ _ _ _ _ erefl; subst.
  exists l.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma lam_invX Γ A1 A2 B C m s1 s2 r t1 t2 t3 l :
  Γ ⊢ Lam A1 m s1 t1 : C : t2 ->
  C <: Pi A2 B s2 r t3 ->
  [A2 :{s2} Γ] ⊢ B : r @ l : U ->
  A2 :{s2} Γ ⊢ m : B : r.
Proof.
  move e:(Lam A1 m s1 t1)=>n tpL.
  elim: tpL A1 A2 B m s1 s2 r t1 t3 l e=>//{Γ C n t2}.
  move=>Γ A B m s r t i k tyP ihP tym ihm A1 A2 B0 m0
    s1 s2 t2 t3 r0 l[e1 e2 e3 e4]/sub_pi_inv[c[sbB[e5[e6 e7]]]] tyB0; subst.
  { move:tyP=>/pi_inv[l0[tyA[_ tyB]]].
    destruct s2.
    apply: clc_conv; eauto.
    apply: context_conv.
    apply: conv_sym; eauto.
    eauto.
    eauto.
    apply: clc_conv; eauto.
    apply: context_conv.
    apply: conv_sym; eauto.
    eauto.
    eauto. }
  move=>Γ A B m s i sb1 tym ihm tyB ihB A1 A2 B0 m0 
    s1 t1 s2 t2 l e sb2 tyB0; subst.
  { apply: ihm; eauto.
    apply: sub_trans; eauto. }
Qed.

Lemma lam_inv Γ m A1 A2 B s1 s2 r t1 t2 t3 x l :
  [Γ] ⊢ Pi A1 B s1 r t1 : x @ l : U ->
  Γ ⊢ Lam A2 m s2 t2 : Pi A1 B s1 r t1 : t3 ->
  A1 :{s1} Γ ⊢ m : B : r.
Proof.
  move=> /pi_inv[i[tyA[_[_ tyB]]]] tyL.
  apply: lam_invX; eauto.
Qed.

Lemma fix_inv Γ k A m C t :
  Γ ⊢ Fix k A m : C : t ->
  exists l,
    A <: C /\ t = U /\ Γ |> U /\
    Γ ⊢ A : U @ l : U /\
    A :U Γ ⊢ m : A.[ren (+1)] : U.
Proof.
  move e:(Fix k A m)=>n tp.
  elim: tp k A m e=>//={Γ n C t}.
  move=>Γ k0 A m l k tyA ihA tym ihm k1 A0 m0[e1 e2 e3]; subst.
  exists l; eauto.
  move=>Γ A B m s i sb1 tym ihm tyB ihB k0 A0 m0 e; subst.
  have[l[sb2[e[k[tyA tym0]]]]]:=ihm _ _ _ erefl.
  exists l.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma ind_inv Γ A B Cs s t :
  Γ ⊢ Ind A Cs s : B : t ->
  exists l1 l2,
    A <: B /\ t = U /\
    arity s l1 A /\
    All1 (constr 0 s) Cs /\
    Γ ⊢ A : U @ l2 : U /\
    All1 (fun C => A :U Γ ⊢ C : s @ l1 : U) Cs.
Proof.
  move e:(Ind A Cs s)=>n tp.
  elim: tp A Cs s e=>//={Γ n B t}.
  move=>Γ A Cs s l1 l2 k ar cCs
    tyA _ tyCs A0 Cs0 s0[e1 e2 e3]; subst.
  exists l1. exists l2.
  repeat split; eauto.
  move=>Γ A B m s i sb tym ihm tyB _ A0 Cs s0 e; subst.
  have[l1[l2[sb'[e[ar[cCs[tyA tyCs]]]]]]]:=ihm _ _ _ erefl.
  exists l1. exists l2.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma constr_inv Γ i I CI s t :
  Γ ⊢ Constr i I s : CI : t ->
  exists A C Cs,
    s = t /\
    Γ |> U /\
    iget i Cs C /\ I = Ind A Cs s /\
    C.[I/] <: CI /\
    Γ ⊢ I : A : U.
Proof.
  move e:(Constr i I s)=>n tp.
  elim: tp i I e=>//={Γ n CI t}.
  move=>Γ A t i C Cs k ig tyI _ i0 I [e1 e2] e3; subst.
  exists A. exists C. exists Cs.
  repeat split; eauto.
  move=>Γ A B m t i sb tym ihm tyB _ i0 I e; subst.
  have[A0[C[Cs[e1[k[ig[e2[sb' tyI]]]]]]]]:=ihm _ _ erefl.
  exists A0. exists C. exists Cs.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.
