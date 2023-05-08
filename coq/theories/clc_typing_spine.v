From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_arity_spine
  clc_validity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive typing_spine :
  context term -> term -> sort -> list term -> term -> sort -> Prop :=
| typing_spine_nil Γ A B s l :
  Γ |> U ->
  A <: B ->
  Γ ⊢ B : s @ l : U ->
  typing_spine Γ A s nil B s
| typing_spine_pi Γ1 Γ2 Γ hd tl T A B B' s r t u l :
  Γ1 |> s ->
  T <: Pi A B s r t ->
  [Γ1] ⊢ Pi A B s r t : t @ l : U ->
  Γ1 ⊢ hd : A : s ->
  Γ1 ∘ Γ2 => Γ ->
  typing_spine Γ2 B.[hd/] r tl B' u ->
  typing_spine Γ T t (hd :: tl) B' u.

Lemma arity_typing_spine Γ A s ms B t :
  arity_spine Γ A s ms B t -> typing_spine Γ A s ms B t.
Proof.
  elim=>{Γ A s ms B t}.
  move=>Γ A s l k tyA.
  apply: typing_spine_nil; eauto.
  move=>Γ1 Γ2 Γ hd tl A B B' s r t u l k tyP tyhd mrg sp ih.
  apply: typing_spine_pi; eauto.
Qed.

Lemma app_typing_spine Γ1 Γ2 Γ m ms A B s t :
  Γ1 ⊢ m : A : s ->
  typing_spine Γ2 A s ms B t ->
  Γ1 ∘ Γ2 => Γ ->
  Γ ⊢ spine m ms : B : t.
Proof.
  move=>tym sp. elim: sp Γ1 Γ m tym=>//={Γ2 A s ms B t}.
  move=>Γ A B s l k sb tyB Γ1 Γ0 m tym mrg.
  { have[e _]:=merge_re_re mrg.
    have->:=merge_pureR mrg k.
    apply: clc_conv; eauto.
    rewrite e.
    rewrite<-pure_re; eauto. }
  move=>Γ1 Γ2 Γ hd tl T A B B' s r t u l k sb tyP tyhd mrg sp ih Γ0 Γ3 m tym mrg'.
  { have[G[mrg1 mrg2]]:=merge_splitL (merge_sym mrg') mrg.
    have[e _]:=merge_re_re mrg1.
    apply: ih; eauto.
    apply: clc_app; eauto.
    apply: merge_sym; eauto.
    apply: clc_conv; eauto.
    rewrite<-e; eauto. }
Qed.

Lemma typing_spine_pi_rcons Γ1 Γ2 Γ A B C n ms s r t u v :
  typing_spine Γ1 A u ms (Pi B C s r t) v ->
  Γ2 |> s ->
  Γ2 ⊢ n : B : s ->
  Γ1 ∘ Γ2 => Γ ->
  typing_spine Γ A u (rcons ms n) C.[n/] r.
Proof.
  move e:(Pi B C s r t)=>T sp.
  elim: sp Γ2 Γ B C s r t n e=>{Γ1 A u ms T v}.
  move=>Γ1 A B s l k1 sb tyB Γ2 Γ B0 C s0 r t n e k2 tyn mrg; subst.
  { rewrite/rcons.
    have[l0[tyB0[sb'[_ tyC]]]]:=pi_inv tyB.
    have[e lt]:=sub_sort_inv sb'; subst.
    have[e _]:=merge_re_re mrg.
    have {}tyC : Γ1 ⊢ C.[n/] : r @ l0 : U.
    { destruct s0.
      have//=:=substitution tyC k2 mrg tyn.
      have->//:=merge_pureR mrg k2.
      have//:=substitutionN tyC tyn. }
    apply: typing_spine_pi.
    apply: k2.
    apply: sb.
    rewrite<-e.
    rewrite<-pure_re; eauto.
    eauto.
    apply: merge_sym; eauto.
    apply: typing_spine_nil; eauto. }
  move=>Γ1 Γ2 Γ hd tl T A B B' s r t u l k1 sb tyP tyhd mrg sp ih
    Γ0 Γ3 B0 C s0 r0 t0 n e k2 tyn mrg'; subst.
  { have[G[mrg1 mrg2]]:=merge_splitR mrg' mrg.
    apply: typing_spine_pi.
    apply: k1.
    apply: sb.
    apply: tyP.
    apply: tyhd.
    apply: mrg2.
    apply: ih; eauto. }
Qed.

Lemma typing_spine_strengthen Γ A B C ms s t l :
  typing_spine Γ B s ms C t ->
  A <: B ->
  [Γ] ⊢ B : s @ l : U ->
  typing_spine Γ A s ms C t.
Proof.
  move=>sp. elim: sp A l=>{Γ B s ms C t}.
  move=>Γ A B s l k sb1 tyB A0 l0 sb2 tyA.
  { apply: typing_spine_nil; eauto.
    apply: sub_trans; eauto. }
  move=>Γ1 Γ2 Γ hd tl T A B B' s r t u l k sb1 tyP tyhd mrg sp ih A0 l0 sb2 tyT.
  { apply: typing_spine_pi; eauto.
    apply: sub_trans; eauto. }
Qed.

Lemma typing_spine_weaken Γ A B C ms s t l :
  typing_spine Γ A s ms B t ->
  B <: C ->
  [Γ] ⊢ C : t @ l : U ->
  typing_spine Γ A s ms C t.
Proof.
  move=>sp. elim: sp C l=>{Γ A s ms B t}.
  move=>Γ A B s l k sb1 tyB C l0 sb2 tyC.
  { apply: typing_spine_nil; eauto.
    apply: sub_trans; eauto.
    rewrite<-pure_re in tyC; eauto. }
  move=>Γ1 Γ2 Γ hd tl T A B B' s r t u l k sb1 tyP tyhd mrg sp ih C l0 sb2 tyC.
  { have[_[_ e]]:=merge_re_re mrg.
    apply: typing_spine_pi; eauto.
    apply: ih; eauto.
    rewrite e; eauto. }
Qed.

Lemma spine'_inv Γ m ms B t :
  ok Γ -> Γ ⊢ spine' m ms : B : t ->
  exists Γ1 Γ2 A s,
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ m : A : s /\
    typing_spine Γ2 A s (rev ms) B t.
Proof.
  move e:(spine' m ms)=>n wf ty.
  elim: ty m ms wf e=>{Γ n B t}.
  move=>Γ s l k m ms wf e.
  { destruct ms; simpl in e; inv e.
    exists Γ. exists Γ. exists (U @ l.+1). exists U.
    repeat split.
    apply: merge_pure; eauto.
    apply: clc_axiom; eauto.
    apply: typing_spine_nil; eauto.
    apply: clc_axiom; eauto. }
  move=>Γ A B s r t i k tyA ihA tyB ihB m ms wf e.
  { destruct ms; simpl in e; inv e.
    exists Γ. exists Γ. exists (t @ i). exists U.
    repeat split.
    apply: merge_pure; eauto.
    apply: clc_pi; eauto.
    apply: typing_spine_nil; eauto.
    apply: clc_axiom; eauto. }
  move=>Γ x A s hs m ms wf e.
  { destruct ms; simpl in e; inv e.
    have[l tyA]:=has_ok wf hs.
    exists Γ. exists [Γ]. exists A. exists s.
    repeat split.
    apply: merge_reR.
    apply: clc_var; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure. }
  move=>Γ A B m s r t i k tyP ihP tym ihm m0 ms wf e.
  { destruct ms; simpl in e; inv e.
    exists Γ. exists [Γ]. exists (Pi A B s r t). exists t.
    repeat split.
    apply: merge_reR.
    apply: clc_lam; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure. }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn m0 ms wf e.
  { have[wf1 wf2]:=merge_context_ok_inv mrg wf.
    have[e0[e1 e2]]:=merge_re_re mrg.
    have[l tyP]:=validity wf1 tym.
    have[l0[tyA[_[_ tyB]]]]:=pi_inv tyP.
    have tyBn: [Γ] ⊢ B.[n/] : r @ l0 : U.
    { have{}mrg:=merge_re3 mrg.
      destruct s.
      replace (r @ l0) with (r @ l0).[n/] by autosubst.
      apply: substitution; eauto.
      replace Γ2 with [Γ2]; eauto.
      rewrite<-pure_re; eauto.
      replace (r @ l0) with (r @ l0).[n/] by autosubst.
      rewrite<-e1.
      apply: substitutionN; eauto. }
    destruct ms; simpl in e; inv e.
    { exists Γ. exists [Γ]. exists B.[n/]. exists r.
      repeat split.
      apply: merge_reR.
      apply: clc_app; eauto.
      apply: typing_spine_nil; eauto.
      apply: re_pure. }
    { have{ihm}[G1[G2[A0[s0[mrg'[tym0 sp]]]]]]:=ihm _ _ wf1 erefl.
      have[G3[mrg1 mrg2]]:=merge_splitR mrg mrg'.
      exists G1. exists G3. exists A0. exists s0.
      repeat split; eauto.
      rewrite rev_cons.
      apply: typing_spine_pi_rcons; eauto. } }
  move=>Γ A Cs s l1 l2 k ar cCs tyA ihA tyCs m ms wf e.
  { destruct ms; simpl in e; inv e.
    exists Γ. exists [Γ]. exists A. exists U.
    repeat split.
    apply: merge_reR.
    apply: clc_indd; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure.
    rewrite<-pure_re; eauto. }
  move=>Γ A s i C Cs I k ig tyI ihI m ms wf e.
  { destruct ms; simpl in e; inv e.
    have[l1[l2[_[_[_[_[_ tyCs]]]]]]]:=ind_inv tyI.
    have tyC:=iget_All1 ig tyCs.
    have//=tyCI:=substitution tyC k (merge_pure k) tyI.
    exists Γ. exists [Γ]. exists C.[I/]. exists s.
    repeat split.
    apply: merge_reR.
    apply: clc_constr; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure.
    rewrite<-pure_re; eauto. }
  move=>Γ1 Γ2 Γ A Q s s' l k Fs Cs m ms I leq ar key mrg
    tym ihm tyQ ihQ tyFs m0 ms0 wf e.
  { destruct ms0; simpl in e; inv e.
    have[wf1 wf2]:=merge_context_ok_inv mrg wf.
    have[e0[e1 e2]]:=merge_re_re mrg.
    have[l0 tysp]:=validity wf1 tym.
    have tyI:=ind_spine (re_pure _) tysp.
    have[l1[l2[_[_[_[cCs[tyA tyCs]]]]]]]:=ind_inv tyI.
    have[sp _]:=ind_spine_inv (re_pure _) ar tysp.
    have{sp}/arity_typing_spine sp:=rearity_spine s' sp ar leq (re_pure _) tyI.
    have spQ:=app_typing_spine tyQ sp (merge_sym (merge_re3 mrg)).
    exists Γ. exists [Γ]. exists (kapp k (spine Q ms) m). exists s'.
    repeat split.
    apply: merge_reR.
    apply: clc_case; eauto.
    destruct k=>//=.
    { have {}mrg : [Γ] ∘ Γ1 => [Γ].
      { replace Γ1 with [Γ1].
        rewrite e1.
        apply: merge_re_id.
        rewrite<-pure_re; eauto. }
      inv leq.
      have:=clc_app key mrg spQ tym.
      apply: typing_spine_nil; eauto.
      apply: re_pure. }
    { apply: typing_spine_nil; eauto.
      apply: re_pure. } }
  move=>Γ k0 A m l k tyA ihA tym ihm m0 ms wf e.
  { destruct ms; simpl in e; inv e.
    exists Γ. exists Γ. exists A. exists U.
    repeat split.
    apply: merge_pure; eauto.
    apply: clc_fix; eauto.
    apply: typing_spine_nil; eauto. }
  move=>Γ A B m s i sb tym ihm tyB _ m0 ms wf e; subst.
  { have[G1[G2[A0[s0[mrg[tym0 sp]]]]]]:=ihm _ _ wf erefl.
    have[_[_ e]]:=merge_re_re mrg.
    exists G1. exists G2. exists A0. exists s0.
    repeat split; eauto.
    apply: typing_spine_weaken; eauto.
    rewrite e; eauto. }
Qed.

Lemma spine_inv Γ m ms B t :
  ok Γ -> Γ ⊢ spine m ms : B : t ->
  exists Γ1 Γ2 A s,
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ m : A : s /\
    typing_spine Γ2 A s ms B t.
Proof.
  rewrite spine_spine'_rev=>wf ty.
  have[G1[G2[A[s[mrg[tym sp]]]]]]:=spine'_inv wf ty.
  rewrite revK in sp.
  exists G1. exists G2. exists A. exists s. eauto.
Qed.
