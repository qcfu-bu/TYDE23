(* This file presents lemmas required for proving the soundness of ι-reductions. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_arity_spine
  clc_validity clc_typing_spine clc_respine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma All2_conv_spine'_tail h xs ys :
  All2 (conv step) xs ys -> spine' h xs === spine' h ys.
Proof.
  elim=>//=.
  move=> m m' ls ls' e a2 ih.
  apply: conv_app; eauto.
Qed.

Lemma All2_conv_spine_tail h xs ys :
  All2 (conv step) xs ys -> spine h xs === spine h ys.
Proof.
  move=>/All2_rev/(All2_conv_spine'_tail h).
  rewrite! spine_spine'_rev; eauto.
Qed.

Lemma eq_spine'_ind A A' Cs Cs' s s' ms ms' :
  spine' (Ind A Cs s) ms = spine' (Ind A' Cs' s') ms' ->
  Ind A Cs s = Ind A' Cs' s' /\ ms = ms'.
Proof.
  elim: ms A A' Cs Cs' s s' ms'=>//=.
  move=>A A' Cs Cs' s s' [|m ms]//=e.
  move=>m ms ih A A' Cs Cs' s s' [|m' ms']//=[e1 e2]; subst.
  move:e1=>/ih[[->->->]->]//.
Qed.

Lemma step_spine'_var x ms n :
  spine' (Var x) ms ~> n ->
  exists ms', n = spine' (Var x) ms' /\ One2 step ms ms'.
Proof with eauto using One2.
  elim: ms x n=>//=.
  move=>x n st. inv st; solve_fix.
  move=>m ms ih x n st. inv st.
  { exfalso; solve_spine'. }
  { move:H2=>/ih[ms'[e st]]; subst.
    exists (m :: ms')... }
  { exists (n' :: ms)... }
  { replace (App (spine' (Var x) ms) m)
      with (spine' (Var x) (m :: ms)) in H by eauto.
    solve_spine_fix. }
Qed.

Lemma step_spine'_ind A Cs s ms n :
  spine' (Ind A Cs s) ms ~> n ->
  exists A' Cs' ms',
    n = spine' (Ind A' Cs' s) ms' /\
      ((Ind A Cs s ~> Ind A' Cs' s /\ ms = ms') \/
       (Ind A Cs s = Ind A' Cs' s /\ One2 step ms ms')).
Proof.
  elim: ms A Cs s n=>//=.
  move=>A Cs s n st. inv st; solve_fix.
  { exists A'. exists Cs. exists nil=>//=.
    split; eauto.
    left; split; eauto.
    constructor; eauto. }
  { exists A. exists Cs'. exists nil=>//=.
    split; eauto.
    left; split; eauto.
    constructor; eauto. }
  move=>m ms ih A Cs s n st. inv st; solve_fix.
  { exfalso; solve_spine'. }
  { move:H2=>/ih[A'[Cs'[ms'[e1[[h e2]|[h e2]]]]]]; subst.
    exists A'. exists Cs'. exists (m :: ms')=>//=.
    split; eauto.
    exists A'. exists Cs'. exists (m :: ms')=>//=.
    split; eauto.
    right; split; eauto.
    constructor; eauto. }
  { exists A. exists Cs. exists (n' :: ms)=>//=.
    split; eauto.
    right; split; eauto.
    constructor; eauto. }
  { replace (App (spine' (Ind A Cs s) ms) m)
      with (spine' (Ind A Cs s) (m :: ms)) in H by eauto.
    solve_spine_fix. }
Qed.

Lemma red_spine'_var x ms n :
  spine' (Var x) ms ~>* n ->
  exists ms', n = spine' (Var x) ms' /\ All2 red ms ms'.
Proof with eauto using All2, All2_red_refl.
  move e:(spine' (Var x) ms)=>m r.
  elim: r x ms e=>{n}.
  move=>x ms e; subst. exists ms...
  move=>y z r ih st x ms e; subst.
  have{ih}[ms'[e rms]]:=ih _ _ erefl; subst.
  have[ms'0[e sms]]:=step_spine'_var st; subst.
  have rms':=One2_step_All2_red sms.
  exists ms'0. split...
  apply: All2_red_trans...
Qed.

Lemma red_spine'_ind A Cs s ms n :
  spine' (Ind A Cs s) ms ~>* n ->
  exists A' Cs' ms',
    n = spine' (Ind A' Cs' s) ms' /\
    Ind A Cs s ~>* Ind A' Cs' s /\ All2 red ms ms'.
Proof with eauto using All2, All2_red_refl.
  move e:(spine' (Ind A Cs s) ms)=>m r.
  elim: r A Cs s ms e=>{n}.
  move=> A Cs s ms e; subst. exists A. exists Cs. exists ms...
  move=>y z r ih st A Cs s ms e; subst.
  have{ih}[A'[Cs'[ms'[e[r' rms]]]]]:=ih _ _ _ _ erefl; subst.
  have[A0[Cs0[ms0[e1[[h e2]|[[e2 e3] e4]]]]]]:=step_spine'_ind st; subst.
  exists A0. exists Cs0. exists ms0. repeat split... apply: starSE...
  exists A0. exists Cs0. exists ms0. repeat split...
  apply: All2_red_trans...
  apply: One2_step_All2_red...
Qed.

Lemma red_spine_var x ms n :
  spine (Var x) ms ~>* n ->
  exists ms', n = spine (Var x) ms' /\ All2 red ms ms'.
Proof.
  rewrite spine_spine'_rev.
  move=>/red_spine'_var[ms'[e rms]]; subst.
  exists (rev ms'). split.
  rewrite spine_spine'_rev.
  by rewrite revK.
  move/All2_rev in rms.
  by rewrite revK in rms.
Qed.

Lemma red_spine_ind A Cs s ms n :
  spine (Ind A Cs s) ms ~>* n ->
  exists A' Cs' ms',
    n = spine (Ind A' Cs' s) ms' /\
    Ind A Cs s ~>* Ind A' Cs' s /\ All2 red ms ms'.
Proof.
  rewrite spine_spine'_rev.
  move=>/red_spine'_ind[A'[Cs'[ms'[e[rI rms]]]]]; subst.
  exists A'. exists Cs'. exists (rev ms'). repeat split; eauto.
  rewrite spine_spine'_rev.
  by rewrite revK.
  move/All2_rev in rms.
  by rewrite revK in rms.
Qed.

Lemma conv_spine'_ind A A' Cs Cs' s s' ms ms' :
  spine' (Ind A Cs s) ms === spine' (Ind A' Cs' s') ms' ->
  Ind A Cs s === Ind A' Cs' s' /\ All2 (conv step) ms ms'.
Proof.
  move=>/church_rosser[x r1 r2].
  move:r1=>/red_spine'_ind[A1[Cs1[ms1[e1[r1 rms1]]]]]; subst.
  move:r2=>/red_spine'_ind[A2[Cs2[ms2[e2[r2 rms2]]]]]; subst.
  move:e2=>/eq_spine'_ind[[e1 e2 e3] e4]; subst.
  split.
  apply: join_conv; eauto.
  apply: All2_conv_trans.
  apply: All2_red_conv; eauto.
  apply: All2_conv_sym.
  apply: All2_red_conv; eauto.
Qed.

Lemma sub_spine'_ind A A' Cs Cs' s s' ms ms' :
  spine' (Ind A Cs s) ms <: spine' (Ind A' Cs' s') ms' ->
  Ind A Cs s === Ind A' Cs' s' /\ All2 (conv step) ms ms'.
Proof.
  move=>[X Y []].
  move=>Z c1 c2.
  { apply: conv_spine'_ind.
    apply: conv_trans; eauto. }
  move=>t l1 l2 leq c1 c2.
  { move:c1=>/church_rosser[Z r1/red_sort_inv e]; subst.
    move:r1=>/red_spine'_ind[A0[Cs0[ms0[e _]]]].
    exfalso; solve_spine'. }
  move=>A0 B1 B2 s0 r t sb c1 c2.
  { move:c1=>/church_rosser[Z r1/red_pi_inv[A1[B3[_[_ e]]]]]; subst.
    move:r1=>/red_spine'_ind[A2[Cs0[ms0[e _]]]].
    exfalso; solve_spine'. }
Qed.

Lemma sub_spine_ind A A' Cs Cs' s s' ms ms' :
  spine (Ind A Cs s) ms <: spine (Ind A' Cs' s') ms' ->
  Ind A Cs s === Ind A' Cs' s' /\ All2 (conv step) ms ms'.
Proof.
  rewrite!spine_spine'_rev=>/sub_spine'_ind[c cms].
  move/All2_rev in cms.
  rewrite!revK in cms.
  eauto.
Qed.

Ltac solve_sub_spine_trans H1 H2 :=
  let x := fresh "x" in
  let h := fresh "h" in
  have x := conv_trans _ H1 H2;
  have h := church_rosser x; inv h;
  match goal with
  | [ H1 : red (Pi _ _ _ _ _) ?x,
      H2 : red (spine (Ind _ _ _) _) ?x |- _ ] =>
    move: H1=>/red_pi_inv; firstorder; subst;
    move: H2=>/red_spine_ind; firstorder; subst;
    solve_spine
  end.

Ltac solve_sub_spine' :=
  match goal with
  | [ H : spine (Ind _ _ _ ) _ === Pi _ _ _ _ _ |- _ ] =>
    let h := fresh "h" in
    have h := church_rosser H; inv h
  | [ H : Pi _ _ _ _ _ === spine (Ind _ _ _ ) _ |- _ ] =>
    let h := fresh "h" in
    have h := church_rosser H; inv h
  | _ => solve_conv
  end;
  match goal with
  | [ H1 : red (Pi _ _ _ _ _) ?x,
      H2 : red (spine (Ind _ _ _) _) ?x |- _ ] =>
    move: H1=>/red_pi_inv; firstorder; subst;
    move: H2=>/red_spine_ind; firstorder; subst;
    solve_spine
  end.

Ltac solve_sub_spine :=
  match goal with
  | [ H : spine (Ind _ _ _ ) _ <: Pi _ _ _ _ _ |- _ ] =>
    move: H=>[_ _ []]; intros
  | [ H : Pi _ _ _ _ _ <: spine (Ind _ _ _ ) _ |- _ ] =>
    move: H=>[_ _ []]; intros
  | _ => solve_sub
  end;
  try match goal with
  | [ H1 : spine (Ind _ _ _) _ === ?x,
      H2 : ?x === Pi _ _ _ _ _ |- _ ] =>
    solve_sub_spine_trans H1 H2
  | [ H1 : ?x === spine (Ind _ _ _) _,
      H2 : Pi _ _ _ _ _ === ?x |- _ ] =>
    solve_sub_spine_trans H2 H1
  | _ => solve_sub_spine'
  end.

Lemma typing_spine_ind_ind Γ A1 A2 Cs1 Cs2 s1 s2 ms1 ms2 ms u v :
  typing_spine Γ
    (spine (Ind A1 Cs1 s1) ms1) u ms
    (spine (Ind A2 Cs2 s2) ms2) v ->
  Ind A1 Cs1 s1 === Ind A2 Cs2 s2 /\ u = v.
Proof.
  move e1:(spine (Ind A1 Cs1 s1) ms1)=>n1.
  move e2:(spine (Ind A2 Cs2 s2) ms2)=>n2 sp.
  elim: sp A1 A2 Cs1 Cs2 s1 s2 ms1 ms2 e1 e2=>{Γ n1 n2 ms u v};
  try solve[intros; subst; exfalso; solve_sub_spine].
  move=>Γ A B s l k sb tyB A1 A2 Cs1 Cs2 s1 s2 ms1 ms2 e1 e2; subst.
  move: sb=>/sub_spine_ind[c _]//.
Qed.

Lemma typing_spine_constr_ind Γ I C A A' Cs Cs' s s' ms ms' n u v :
  constr n s C ->
  typing_spine Γ C.[I] u ms (spine (Ind A' Cs' s') ms') v ->
  I n = Ind A Cs s -> I n === Ind A' Cs' s' /\ u = v.
Proof.
  move=>cst. elim: cst Γ I A A' Cs Cs' s' ms ms' u v=>//={C s n}.
  move=>x s ms nms Γ I A A' Cs Cs' s' ms1 ms2 u v sp e.
  { move: sp.
    rewrite spine_subst=>//=.
    rewrite e.
    move=>/typing_spine_ind_ind//. }
  move=>s t x A B leq pA nB cB ih Γ I A1 A2 Cs Cs' s' ms ms' u v sp e.
  { inv sp; try solve[exfalso; solve_sub_spine].
    have[e12 _]:=merge_re_re H3.
    have[cA[sB[e1[e2 e3]]]]:=sub_pi_inv H0; subst.
    have sb : B.[up I].[hd/] <: B0.[hd/].
    { apply: sub_subst; eauto. }
    asimpl in sb.
    have ex : (hd .: I) x.+1 = Ind A1 Cs u by autosubst.
    have[l0[tyA0[_[_ tyB0]]]]:=pi_inv H1.
    have{}tyB0: [Γ1] ⊢ B0.[hd/] : u @ l0 : U.
    { replace (u @ l0) with (u @ l0).[hd/] by autosubst.
      destruct s0.
      apply: substitution; eauto.
      rewrite<-!pure_re; eauto.
      apply: merge_pure; eauto.
      apply: substitutionN; eauto. }
    rewrite e12 in tyB0.
    have sp:=typing_spine_strengthen H4 sb tyB0.
    have//:=ih _ _ _ _ _ _ _ _ _ _ _ sp ex. }
  move=>s t x A B leq nA cB ih Γ I A1 A2 Cs Cs' s' ms ms' u v sp e.
  { inv sp; try solve[exfalso; solve_sub_spine].
    have[e12 _]:=merge_re_re H3.
    have[cA[sB[e1[e2 e3]]]]:=sub_pi_inv H0; subst.
    have sb : B.[up I].[hd/] <: B0.[hd/].
    { apply: sub_subst; eauto. }
    asimpl in sb.
    have ex : (hd .: I) x.+1 = Ind A1 Cs u by autosubst.
    have[l0[tyA0[_[_ tyB0]]]]:=pi_inv H1.
    have{}tyB0: [Γ1] ⊢ B0.[hd/] : u @ l0 : U.
    { replace (u @ l0) with (u @ l0).[hd/] by autosubst.
      destruct s0.
      apply: substitution; eauto.
      rewrite<-!pure_re; eauto.
      apply: merge_pure; eauto.
      apply: substitutionN; eauto. }
    rewrite e12 in tyB0.
    have sp:=typing_spine_strengthen H4 sb tyB0.
    have//:=ih _ _ _ _ _ _ _ _ _ _ _ sp ex. }
Qed.

Lemma typine_spine_ind_Q1 Γ A Q Cs ms1 ms2 ms s t l u v :
  typing_spine Γ (spine (Ind A Cs s) ms1) u ms (spine (Ind A Cs s) ms2) v ->
  [Γ] ⊢ spine Q ms2 : t @ l : U ->
  typing_spine Γ (spine Q ms1) t ms (spine Q ms2) t.
Proof.
  move e1:(spine (Ind A Cs s) ms1)=>n1.
  move e2:(spine (Ind A Cs s) ms2)=>n2 sp.
  elim: sp A Q Cs ms1 ms2 s t l e1 e2=>{Γ n1 n2 u v ms};
  try solve[intros; subst; exfalso; solve_sub_spine].
  move=>Γ A B s l k sb tyB A0 Q Cs ms1 ms2 s0 t l0 e1 e2 tyQ; subst.
  have[_ ems]:=sub_spine_ind sb.
  apply: typing_spine_nil; eauto.
  apply: conv_sub.
  apply: All2_conv_spine_tail; eauto.
  rewrite<-pure_re in tyQ; eauto.
Qed.

Lemma typing_spine_ind_Q2 Γ A Q c Cs ms1 ms2 ms s t l u v :
  typing_spine Γ (spine (Ind A Cs s) ms1) u ms (spine (Ind A Cs s) ms2) v ->
  [Γ] ⊢ spine Q ms2 : Pi (spine (Ind A Cs s) ms2) (t @ l) u U U : U ->
  [Γ] ⊢ c : spine (Ind A Cs s) ms1 : u ->
  typing_spine Γ (App (spine Q ms1) c) t ms (App (spine Q ms2) (spine c ms)) t.
Proof.
  move e1:(spine (Ind A Cs s) ms1)=>n1.
  move e2:(spine (Ind A Cs s) ms2)=>n2 sp.
  elim: sp A Q c Cs ms1 ms2 s t l e1 e2=>{Γ n1 n2 u v ms};
  try solve[intros; subst; exfalso; solve_sub_spine].
  move=>Γ A B s l k sb tyB A0 Q c Cs ms1 ms2 s0 t l0 e1 e2 tyQ tyc; subst.
  have{}tyc:[Γ] ⊢ c : spine (Ind A0 Cs s0) ms2 : s.
  { apply: clc_conv; eauto.
    rewrite<-re_invo; eauto.
    rewrite<-pure_re; eauto. }
  have k': [Γ] |> s.
  { destruct s. apply: re_pure. apply: key_impure. }
  have//=tyapp:=clc_app k' (merge_re_id _) tyQ tyc.
  have[_ ems]:=sub_spine_ind sb.
  apply: typing_spine_nil; eauto.
  apply: conv_sub.
  apply: conv_app; eauto.
  apply: All2_conv_spine_tail; eauto.
  rewrite<-pure_re in tyapp; eauto.
Qed.

Lemma typing_spine_constrU Γ A Cs C I Q ms1 ms2 c s v l1 l2 n :
  constr n U C ->
  typing_spine Γ C.[I] U ms1 (spine (I n) ms2) v ->
  (I n = Ind A Cs U) ->
  (forall x, ~I n = Var x) ->
  [Γ] ⊢ C.[I] : U @ l1 : U ->
  [Γ] ⊢ c : C.[I] : U ->
  [Γ] ⊢ Ind A Cs U : A : U ->
  [Γ] ⊢ Q : rearity U s (Ind A Cs U) A : U ->
  [Γ] ⊢ spine Q ms2 : Pi (spine (Ind A Cs U) ms2) (s @ l2) U U U : U ->
  let T := respine U s Q c C.[I] in
  typing_spine Γ T.2 T.1 ms1 (App (spine Q ms2) (spine c ms1)) s.
Proof.
  move e:(U)=>u cst.
  elim: cst Γ A Cs I Q ms1 ms2 c s v l1 l2 e=>//={C n u}.
  move=>x s ms nms Γ A Cs I Q ms1 ms2 c s0 v l1 l2 e
    sp h1 h2 tyx tyc tyI tyQ spQ; subst.
  { rewrite spine_subst=>//=.
    rewrite h1.
    pose proof (respine_spine_ind Q c A Cs U U s0 ms..[I]) as [e1 e2].
    rewrite spine_subst in tyc. simpl in tyc.
    rewrite spine_subst in sp. simpl in sp.
    rewrite h1 in tyc.
    rewrite h1 in sp.
    rewrite e1 e2=>//=.
    apply: typing_spine_ind_Q2; eauto. }
  move=>s t x A B leq pA nB cB ihB Γ A0 Cs I Q ms1 ms2 c s0 v l1 l2 e
    sp h1 h2 tyP tyc tyI tyQ spQ; subst.
  { rewrite h1 in sp.
    inv sp; try solve[exfalso; solve_sub_spine].
    have[cA[sB[e1[e2 e3]]]]:=sub_pi_inv H0; subst.
    have[e12[e1 e2]]:=merge_re_re H3.
    have[l3[tyA1[_[_ tyB1]]]]:=pi_inv tyP.
    have[l4[tyA2[_[_ tyB2]]]]:=pi_inv H1.
    have[l5[l6[_[_[ar _]]]]]:=ind_inv tyI.
    have ar1:=arity_ren (+1) ar.
    have h3 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U.
    { asimpl. rewrite h1. autosubst. }
    have h4 : [A1 :U Γ] ⊢ up I x.+1 : A0.[ren (+1)] : U.
    { asimpl. rewrite h1. apply: eweakeningU; eauto. }
    have h5 : [A1 :U Γ] ⊢ Q.[ren (+1)] : (rearity U s0 (Ind A0 Cs U) A0).[ren (+1)] : U.
    { asimpl. apply: eweakeningU; eauto. }
    erewrite rearity_subst in h5; eauto.
    inv leq.
    have h6 : [A1 :U Γ] ⊢ B.[up I] : U @ l3 : U.
    { apply: context_conv.
      apply: conv_sym; eauto.
      rewrite<-re_invo; eauto.
      eauto. }
    have mrg' := merge_re3 H3.
    have h7 : [Γ2] ⊢ hd : A1 : U.
    { rewrite<-e12. rewrite<-pure_re; eauto. }
    have h8 : [Γ2] ⊢ B.[hd .: I] : U @ l3 : U.
    { rewrite e2. simpl in h6; rewrite<-e1 in h6.
      have:=substitution h6 (re_pure _) mrg' h7.
      by asimpl. }
    have h9 : B.[up I].[hd/] <: B0.[hd/].
    { apply: sub_subst; eauto. }
    asimpl in h9.
    rewrite e12 in tyB2.
    have h10 : [Γ2] ⊢ B0.[hd/] : U @ l4 : U.
    { replace (U @ l4) with (U @ l4).[hd/] by autosubst.
      rewrite e2.
      apply: substitution; eauto.
      replace Γ1 with [Γ1].
      apply: merge_sym; eauto.
      rewrite<-pure_re; eauto. }
    have h11 : typing_spine Γ2 B.[hd .: I] U tl (spine (Ind A0 Cs U) ms2) v.
    { apply: typing_spine_strengthen; eauto. }
    have h12 : A1 :U [Γ] |> U.
    { constructor. apply: re_pure. }
    have h13 : [A1 :U Γ] ⊢ c.[ren (+1)] : (Pi A.[I] B.[up I] U U U).[ren (+1)] : U.
    { apply: eweakeningU; eauto. }
    asimpl in h13.
    have h15 : [A1 :U Γ] ⊢ ids 0 : A.[I].[ren (+1)] : U.
    { apply: context_conv.
      apply: conv_sym; eauto.
      rewrite<-re_invo; eauto.
      apply: clc_var.
      constructor.
      apply: re_pure. }
    asimpl in h15.
    have h16:=clc_app (re_pure (A1 :U Γ)) (merge_re_id _) h13 h15.
    asimpl in h16.
    have h17 : [Γ2] ⊢ App c hd : B.[up I].[hd/] : U.
    { have mrg: [Γ] ∘ Γ1 => [Γ2].
      replace Γ1 with [Γ1].
      rewrite e1 e2. apply: merge_re_id.
      rewrite<-pure_re; eauto.
      have:=substitution h16 H mrg H2.
      by asimpl. }
    have//=[l0 ty]:=constr_respineU cB ar1 h3 h4 h5 h6 h16.
    rewrite<-e1 in ty.
    rewrite<-pure_re in ty; eauto.
    replace (Var 0) with (ids 0) by autosubst.
    remember (respine U s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as h.
    destruct h=>//=. simpl in ty.
    apply: typing_spine_pi.
    apply: (re_pure Γ1).
    apply: conv_sub.
    apply: conv_pi; eauto.
    rewrite<-re_invo.
    apply: clc_pi_max=>//=; eauto.
    apply: re_pure.
    rewrite<-re_invo.
    rewrite<-pure_re; eauto.
    rewrite<-pure_re; eauto.
    rewrite<-pure_re; eauto.
    have neq: ∀ y : var, up I x.+1 ≠ Var y.
    { asimpl. apply: ren_var_false; eauto. }
    pose proof
      (constr_respine_subst cB h3 neq Q.[ren (+1)]
        (App c.[ren (+1)] (ids 0)) U s0 (hd .: ids)) as [e4 e5].
    remember (respine U s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as h.
    destruct h.
    asimpl in e4.
    asimpl in e5.
    inv Heqh.
    rewrite e5.
    apply: ihB; eauto.
    asimpl. rewrite h1; eauto.
    replace B.[hd .: I] with B.[up I].[hd/] by autosubst.
    eauto.
    rewrite e2; eauto.
    rewrite e2; eauto.
    rewrite e2; eauto. }
  move=>s t x A B leq nA cB ihB Γ A0 Cs I Q ms1 ms2 c s0 v l1 l2 e
    sp h1 h2 tyP tyc tyI tyQ spQ; subst.
  { rewrite h1 in sp.
    inv sp; try solve[exfalso; solve_sub_spine].
    have[cA[sB[e1[e2 e3]]]]:=sub_pi_inv H0; subst.
    have[e12[e1 e2]]:=merge_re_re H3.
    have[l3[tyA1[_[_ tyB1]]]]:=pi_inv tyP.
    have[l4[tyA2[_[_ tyB2]]]]:=pi_inv H1.
    have[l5[l6[_[_[ar _]]]]]:=ind_inv tyI.
    have ar1:=arity_ren (+1) ar.
    have h3 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U.
    { asimpl. rewrite h1. autosubst. }
    have h4 : [A1 :U Γ] ⊢ up I x.+1 : A0.[ren (+1)] : U.
    { asimpl. rewrite h1. apply: eweakeningU; eauto. }
    have h5 : [A1 :U Γ] ⊢ Q.[ren (+1)] : (rearity U s0 (Ind A0 Cs U) A0).[ren (+1)] : U.
    { asimpl. apply: eweakeningU; eauto. }
    erewrite rearity_subst in h5; eauto.
    inv leq.
    have h6 : [A1 :U Γ] ⊢ B.[up I] : U @ l3 : U.
    { apply: context_conv.
      apply: conv_sym; eauto.
      rewrite<-re_invo; eauto.
      eauto. }
    have mrg' := merge_re3 H3.
    have h7 : [Γ2] ⊢ hd : A1 : U.
    { rewrite<-e12. rewrite<-pure_re; eauto. }
    have h8 : [Γ2] ⊢ B.[hd .: I] : U @ l3 : U.
    { rewrite e2. simpl in h6; rewrite<-e1 in h6.
      have:=substitution h6 (re_pure _) mrg' h7.
      by asimpl. }
    have h9 : B.[up I].[hd/] <: B0.[hd/].
    { apply: sub_subst; eauto. }
    asimpl in h9.
    rewrite e12 in tyB2.
    have h10 : [Γ2] ⊢ B0.[hd/] : U @ l4 : U.
    { replace (U @ l4) with (U @ l4).[hd/] by autosubst.
      rewrite e2.
      apply: substitution; eauto.
      replace Γ1 with [Γ1].
      apply: merge_sym; eauto.
      rewrite<-pure_re; eauto. }
    have h11 : typing_spine Γ2 B.[hd .: I] U tl (spine (Ind A0 Cs U) ms2) v.
    { apply: typing_spine_strengthen; eauto. }
    have h12 : A1 :U [Γ] |> U.
    { constructor. apply: re_pure. }
    have h13 : [A1 :U Γ] ⊢ c.[ren (+1)] : (Pi A.[I] B.[up I] U U U).[ren (+1)] : U.
    { apply: eweakeningU; eauto. }
    asimpl in h13.
    have h15 : [A1 :U Γ] ⊢ ids 0 : A.[I].[ren (+1)] : U.
    { apply: context_conv.
      apply: conv_sym; eauto.
      rewrite<-re_invo; eauto.
      apply: clc_var.
      constructor.
      apply: re_pure. }
    asimpl in h15.
    have h16:=clc_app (re_pure (A1 :U Γ)) (merge_re_id _) h13 h15.
    asimpl in h16.
    have h17 : [Γ2] ⊢ App c hd : B.[up I].[hd/] : U.
    { have mrg: [Γ] ∘ Γ1 => [Γ2].
      replace Γ1 with [Γ1].
      rewrite e1 e2. apply: merge_re_id.
      rewrite<-pure_re; eauto.
      have:=substitution h16 H mrg H2.
      by asimpl. }
    have//=[l0 ty]:=constr_respineU cB ar1 h3 h4 h5 h6 h16.
    rewrite<-e1 in ty.
    rewrite<-pure_re in ty; eauto.
    replace (Var 0) with (ids 0) by autosubst.
    remember (respine U s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as h.
    destruct h=>//=. simpl in ty.
    apply: typing_spine_pi.
    apply: (re_pure Γ1).
    apply: conv_sub.
    apply: conv_pi; eauto.
    rewrite<-re_invo.
    apply: clc_pi_max=>//=; eauto.
    apply: re_pure.
    rewrite<-re_invo.
    rewrite<-pure_re; eauto.
    rewrite<-pure_re; eauto.
    rewrite<-pure_re; eauto.
    have neq: ∀ y : var, up I x.+1 ≠ Var y.
    { asimpl. apply: ren_var_false; eauto. }
    pose proof
      (constr_respine_subst cB h3 neq Q.[ren (+1)]
        (App c.[ren (+1)] (ids 0)) U s0 (hd .: ids)) as [e4 e5].
    remember (respine U s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as h.
    destruct h.
    asimpl in e4.
    asimpl in e5.
    inv Heqh.
    rewrite e5.
    apply: ihB; eauto.
    asimpl. rewrite h1; eauto.
    replace B.[hd .: I] with B.[up I].[hd/] by autosubst.
    eauto.
    rewrite e2; eauto.
    rewrite e2; eauto.
    rewrite e2; eauto. }
Qed.

Lemma typing_spine_constrL Γ A Cs C I Q ms1 ms2 c s s' v l1 l2 n :
  constr n s C ->
  typing_spine Γ C.[I] s ms1 (spine (I n) ms2) v ->
  (I n = Ind A Cs s) ->
  (forall x, ~I n = Var x) ->
  [Γ] ⊢ C.[I] : s @ l1 : U ->
  [Γ] ⊢ Ind A Cs s : A : U ->
  [Γ] ⊢ Q : rearity L s' (Ind A Cs s) A : U ->
  [Γ] ⊢ spine Q ms2 : s' @ l2 : U ->
  let T := respine L s' Q c C.[I] in
  typing_spine Γ T.2 T.1 ms1 (spine Q ms2) s'.
Proof.
  move=>cst.
  elim: cst Γ A Cs I Q ms1 ms2 c s' v l1 l2=>//={C n s}.
  move=>x s ms nms Γ A Cs I Q ms1 ms2 c s0 v l1 l2
    sp h1 h2 tyx tyI tyQ spQ; subst.
  { rewrite spine_subst=>//=.
    rewrite h1.
    pose proof (respine_spine_ind Q c A Cs L s s0 ms..[I]) as [e1 e2].
    rewrite spine_subst in sp. simpl in sp.
    rewrite h1 in sp.
    rewrite e1 e2=>//=.
    apply: typine_spine_ind_Q1; eauto. }
  move=>s t x A B leq pA nB cB ihB Γ A0 Cs I Q ms1 ms2 c s0 v l1 l2
    sp h1 h2 tyP tyI tyQ spQ; subst.
  { rewrite h1 in sp.
    inv sp; try solve[exfalso; solve_sub_spine].
    have[cA[sB[e1[e2 e3]]]]:=sub_pi_inv H0; subst.
    have[e12[e1 e2]]:=merge_re_re H3.
    have[l3[tyA1[_[_ tyB1]]]]:=pi_inv tyP.
    have[l4[tyA2[_[_ tyB2]]]]:=pi_inv H1.
    have[l5[l6[_[_[ar _]]]]]:=ind_inv tyI.
    have ar1:=arity_ren (+1) ar.
    have h3 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] r.
    { asimpl. rewrite h1. autosubst. }
    have h4 : [A1 :{s1} Γ] ⊢ up I x.+1 : A0.[ren (+1)] : U.
    { asimpl. rewrite h1.
      destruct s1.
      apply: eweakeningU; eauto.
      apply: eweakeningN; eauto. }
    have h5 : [A1 :{s1} Γ] ⊢ Q.[ren (+1)] : (rearity L s0 (Ind A0 Cs r) A0).[ren (+1)] : U.
    { asimpl. destruct s1.
      apply: eweakeningU; eauto.
      apply: eweakeningN; eauto. }
    erewrite rearity_subst in h5; eauto.
    have h6 : [A1 :{s1} Γ] ⊢ B.[up I] : r @ l3 : U.
    { destruct s1; eauto.
      apply: context_conv.
      apply: conv_sym; eauto.
      rewrite<-re_invo; eauto.
      eauto. }
    have h7 : [Γ2] ⊢ B.[hd .: I] : r @ l3 : U.
    { destruct s1.
      have mrg':[Γ] ∘ Γ1 => [Γ2].
      replace Γ1 with [Γ1].
      rewrite e1 e2. apply: merge_re_id.
      rewrite<-pure_re; eauto.
      have:=substitution h6 H mrg' H2.
      by asimpl.
      have:=substitutionN h6 H2.
      rewrite e2. by asimpl. }
    have h8 : B.[up I].[hd/] <: B0.[hd/].
    { apply: sub_subst; eauto. }
    asimpl in h8.
    rewrite e12 in tyB2.
    have h9 : [Γ2] ⊢ B0.[hd/] : r @ l4 : U.
    { destruct s1.
      have mrg':[Γ2] ∘ Γ1 => [Γ2].
      replace Γ1 with [Γ1].
      rewrite e12. apply: merge_re_id.
      rewrite<-pure_re; eauto.
      have:=substitution tyB2 H mrg' H2.
      by asimpl.
      have//:=substitutionN tyB2 H2. }
    have h10 : typing_spine Γ2 B.[hd .: I] r tl (spine (Ind A0 Cs r) ms2) v.
    { apply: typing_spine_strengthen; eauto. }
    pose proof (constr_respineL (App c.[ren (+1)] (ids 0)) cB ar1 h3 h4 h5 h6) as [l0 ty].
    replace (Var 0) with (ids 0) by autosubst.
    remember (respine L s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as h.
    destruct h=>//=. simpl in ty.
    apply: typing_spine_pi.
    apply: H.
    apply: conv_sub.
    apply: conv_pi; eauto.
    apply: clc_pi_max=>//=; eauto.
    apply: re_pure.
    rewrite<-re_invo.
    rewrite e1; eauto.
    eauto.
    eauto.
    have neq: ∀ y : var, up I x.+1 ≠ Var y.
    { asimpl. apply: ren_var_false; eauto. }
    pose proof
      (constr_respine_subst cB h3 neq Q.[ren (+1)]
        (App c.[ren (+1)] (ids 0)) L s0 (hd .: ids)) as [e4 e5].
    remember (respine L s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as h.
    destruct h.
    asimpl in e4.
    asimpl in e5.
    inv Heqh.
    rewrite e5.
    apply: ihB; eauto.
    asimpl. rewrite h1; eauto.
    replace B.[hd .: I] with B.[up I].[hd/] by autosubst.
    rewrite e2; eauto.
    rewrite e2; eauto.
    rewrite e2; eauto. }
  move=>s t x A B leq nA cB ihB Γ A0 Cs I Q ms1 ms2 c s0 v l1 l2
    sp h1 h2 tyP tyI tyQ spQ; subst.
  { rewrite h1 in sp.
    inv sp; try solve[exfalso; solve_sub_spine].
    have[cA[sB[e1[e2 e3]]]]:=sub_pi_inv H0; subst.
    have[e12[e1 e2]]:=merge_re_re H3.
    have[l3[tyA1[_[_ tyB1]]]]:=pi_inv tyP.
    have[l4[tyA2[_[_ tyB2]]]]:=pi_inv H1.
    have[l5[l6[_[_[ar _]]]]]:=ind_inv tyI.
    have ar1:=arity_ren (+1) ar.
    have h3 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] r.
    { asimpl. rewrite h1. autosubst. }
    have h4 : [A1 :{s1} Γ] ⊢ up I x.+1 : A0.[ren (+1)] : U.
    { asimpl. rewrite h1.
      destruct s1.
      apply: eweakeningU; eauto.
      apply: eweakeningN; eauto. }
    have h5 : [A1 :{s1} Γ] ⊢ Q.[ren (+1)] : (rearity L s0 (Ind A0 Cs r) A0).[ren (+1)] : U.
    { asimpl. destruct s1.
      apply: eweakeningU; eauto.
      apply: eweakeningN; eauto. }
    erewrite rearity_subst in h5; eauto.
    have h6 : [A1 :{s1} Γ] ⊢ B.[up I] : r @ l3 : U.
    { destruct s1; eauto.
      apply: context_conv.
      apply: conv_sym; eauto.
      rewrite<-re_invo; eauto.
      eauto. }
    have h7 : [Γ2] ⊢ B.[hd .: I] : r @ l3 : U.
    { destruct s1.
      have mrg':[Γ] ∘ Γ1 => [Γ2].
      replace Γ1 with [Γ1].
      rewrite e1 e2. apply: merge_re_id.
      rewrite<-pure_re; eauto.
      have:=substitution h6 H mrg' H2.
      by asimpl.
      have:=substitutionN h6 H2.
      rewrite e2. by asimpl. }
    have h8 : B.[up I].[hd/] <: B0.[hd/].
    { apply: sub_subst; eauto. }
    asimpl in h8.
    rewrite e12 in tyB2.
    have h9 : [Γ2] ⊢ B0.[hd/] : r @ l4 : U.
    { destruct s1.
      have mrg':[Γ2] ∘ Γ1 => [Γ2].
      replace Γ1 with [Γ1].
      rewrite e12. apply: merge_re_id.
      rewrite<-pure_re; eauto.
      have:=substitution tyB2 H mrg' H2.
      by asimpl.
      have//:=substitutionN tyB2 H2. }
    have h10 : typing_spine Γ2 B.[hd .: I] r tl (spine (Ind A0 Cs r) ms2) v.
    { apply: typing_spine_strengthen; eauto. }
    pose proof (constr_respineL (App c.[ren (+1)] (ids 0)) cB ar1 h3 h4 h5 h6) as [l0 ty].
    replace (Var 0) with (ids 0) by autosubst.
    remember (respine L s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as h.
    destruct h=>//=. simpl in ty.
    apply: typing_spine_pi.
    apply: H.
    apply: conv_sub.
    apply: conv_pi; eauto.
    apply: clc_pi_max=>//=; eauto.
    apply: re_pure.
    rewrite<-re_invo.
    rewrite e1; eauto.
    eauto.
    eauto.
    have neq: ∀ y : var, up I x.+1 ≠ Var y.
    { asimpl. apply: ren_var_false; eauto. }
    pose proof
      (constr_respine_subst cB h3 neq Q.[ren (+1)]
        (App c.[ren (+1)] (ids 0)) L s0 (hd .: ids)) as [e4 e5].
    remember (respine L s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as h.
    destruct h.
    asimpl in e4.
    asimpl in e5.
    inv Heqh.
    rewrite e5.
    apply: ihB; eauto.
    asimpl. rewrite h1; eauto.
    replace B.[hd .: I] with B.[up I].[hd/] by autosubst.
    rewrite e2; eauto.
    rewrite e2; eauto.
    rewrite e2; eauto. }
Qed.
