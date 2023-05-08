From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_arity_spine
  clc_validity clc_typing_spine clc_respine clc_iota_lemma
  clc_soundness clc_resolution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive resolve_spine : context term -> list term -> list term -> Prop :=
| resolve_spine_nil Θ :
  Θ |> U ->
  resolve_spine Θ nil nil
| resolve_spine_cons Θ1 Θ2 Θ m m' ms ms' :
  Θ1 ∘ Θ2 => Θ ->
  resolve Θ1 m m' ->
  resolve_spine Θ2 ms ms' ->
  resolve_spine Θ (m :: ms) (m' :: ms').

Lemma resolve_spine_size Θ ms1 ms2 :
  resolve_spine Θ ms1 ms2 -> size ms1 = size ms2.
Proof.
  elim=>//.
  move=>Θ1 Θ2 Θ0 m m' ms ms' mrg rsm rsp e//=.
  by rewrite e.
Qed.

Lemma app_resolve_spine Θ1 Θ2 Θ m m' ms ms' :
  resolve Θ1 m m' ->
  resolve_spine Θ2 ms ms' ->
  Θ1 ∘ Θ2 => Θ ->
  resolve Θ (spine m ms) (spine m' ms').
Proof.
  move=>rsm rsp. elim: rsp Θ1 Θ m m' rsm=>//={Θ2 ms ms'}.
  move=>Θ2 k Θ1 Θ m m' rsm mrg.
  have->//:=merge_pureR mrg k.
  move=>Θ1 Θ2 Θ m m' ms ms' mrg1 rsm1 rsp ih Θ0 Θ3 m0 m1 rsm2 mrg2.
  have[G1[mrg3 mrg4]]:=merge_splitL (merge_sym mrg2) mrg1.
  apply: ih; eauto.
  apply: resolve_app.
  apply: merge_sym; eauto.
  all: eauto.
Qed.

Lemma resolve_spine_append Θ1 Θ2 Θ xs xs' ys ys' :
  resolve_spine Θ1 xs xs' ->
  resolve_spine Θ2 ys ys' ->
  Θ1 ∘ Θ2 => Θ ->
  resolve_spine Θ (xs ++ ys) (xs' ++ ys').
Proof.
  move=>rs. elim: rs Θ2 Θ ys ys'=>//={Θ1 xs xs'}.
  move=>Θ1 k Θ2 Θ ys ys' rys mrg.
  have->//:=merge_pureL mrg k.
  move=>Θ1 Θ2 Θ m m' ms ms' mrg1 rsm rsms ih Θ0 Θ3 ys ys' rys mrg2.
  have[G[mrg3 mrg4]]:=merge_splitR mrg2 mrg1.
  econstructor; eauto.
Qed.

Lemma resolve_spine_rcons Θ1 Θ2 Θ xs xs' x x' :
  resolve_spine Θ1 xs xs' ->
  resolve Θ2 x x' ->
  Θ1 ∘ Θ2 => Θ ->
  resolve_spine Θ (rcons xs x) (rcons xs' x').
Proof.
  move=>rxs rx mrg.
  rewrite<-!cats1.
  apply: resolve_spine_append; eauto.
  have mrg' : Θ2 ∘ [Θ2] => Θ2.
    apply: merge_reR.
  econstructor; eauto.
  constructor.
  apply: re_pure.
Qed.

Lemma ptr_spine_inv Θ l ms n :
  resolve Θ (spine (Ptr l) ms) n ->
  exists Θ1 Θ2 m' ms',
    Θ1 ∘ Θ2 => Θ /\
    n = (spine m' ms') /\
    resolve Θ1 (Ptr l) m' /\
    resolve_spine Θ2 ms ms'.
Proof.
  move e:(spine (Ptr l) ms)=>x rs.
  elim: rs l ms e=>{Θ n x}.
  all: try solve[intros; exfalso; solve_spine].
  move=>Θ1 Θ2 Θ m m' n n' mrg rm ihm rn ihn l ms e.
  { have[ms1[e1 e2]]:=ptr_spine_app_inv e; subst.
    have[G1[G2[mx[msx[mrg1[e1[rx rsx]]]]]]]:=ihm _ _ erefl; subst.
    have[Gx[mrg2 mrg3]]:=merge_splitR mrg mrg1.
    exists G1. exists Gx. exists mx. exists (rcons msx n').
    repeat split; eauto.
    rewrite<-spine_app_rcons; eauto.
    apply: resolve_spine_rcons; eauto. }
  move=>Θ Θ' l m m' fr rs ihm l0 ms.
  { have->: Ptr l = spine (Ptr l) nil by eauto.
    move=>/spine_ptr_inj[e1 e2]; subst.
    exists Θ. exists [Θ]. exists m'. exists nil.
    repeat constructor; eauto.
    apply:merge_reR.
    econstructor; eauto.
    apply: re_pure. }
Qed.

Lemma constr_spine_inv Θ i I s m ms :
  resolve Θ (spine (Constr i I s) ms) m ->
  exists I' ms',
    m = spine (Constr i I' s) ms' /\
    resolve [Θ] I I' /\
    resolve_spine Θ ms ms'.
Proof.
  move e:(spine (Constr i I s) ms)=>n rs.
  elim: rs i I s ms e=>{Θ m n}.
  all: try solve[intros; exfalso; solve_spine].
  move=>Θ1 Θ2 Θ m m' n n' mrg rm ihm rn ihn i I s ms e.
  { have[ms1[e1 e2]]:=constr_spine_app_inv e; subst.
    have[I'[ms'[e'[rI rms]]]]:=ihm _ _ _ _ erefl; subst.
    exists I'. exists (rcons ms' n').
    repeat split.
    rewrite spine_app_rcons; eauto.
    have[_[<-_]]//:=merge_re_re mrg.
    apply: resolve_spine_rcons; eauto. }
  move=>Θ i I I' s k rI ihI i0 I0 s0 ms.
  { have->: Constr i I s = spine (Constr i I s) nil by eauto.
    move=>/spine_constr_inj[e1[e2[e3 e4]]]; subst.
    exists I'. exists nil.
    repeat constructor; eauto. 
    rewrite<-pure_re; eauto. }
Qed.
