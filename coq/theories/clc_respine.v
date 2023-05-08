From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_arity_spine
  clc_validity clc_typing_spine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma respine0_spine'_ind Q A Cs s ms :
  respine0 Q (spine' (Ind A Cs s) ms) = spine' Q ms.
Proof.
  elim: ms=>//=.
  move=>m ms ih.
  rewrite ih=>//.
Qed.

Lemma respine_spine'_ind Q c A Cs k s s' ms :
  (respine k s' Q c (spine' (Ind A Cs s) ms)).1 = s' /\
  (respine k s' Q c (spine' (Ind A Cs s) ms)).2 = kapp k (spine' Q ms) c.
Proof.
  elim: ms=>//=.
  destruct k=>//.
  move=>m ms ih.
  destruct k=>//=.
  rewrite respine0_spine'_ind=>//.
  rewrite respine0_spine'_ind=>//.
Qed.

Lemma respine_spine_ind Q c A Cs k s s' ms :
  (respine k s' Q c (spine (Ind A Cs s) ms)).1 = s' /\
  (respine k s' Q c (spine (Ind A Cs s) ms)).2 = kapp k (spine Q ms) c.
Proof.
  rewrite!spine_spine'_rev.
  apply: respine_spine'_ind.
Qed.

Lemma spine'_var x y ms :
  spine' (Var x) ms = Var y -> x = y /\ ms = nil.
Proof. elim: ms=>//=. move=>[->]//. Qed.

Lemma app_false (ls : list term) x : ls ++ [:: x] = nil -> False.
Proof. elim: ls=>//=. Qed.

Lemma rev_nil (ls : list term) : rev ls = nil -> ls = nil.
Proof.
  move=>e.
  have : rev (rev ls) = rev nil by rewrite e.
  rewrite revK.
  rewrite /rev/catrev=>//.
Qed.

Lemma spine_var x y ms :
  spine (Var x) ms = Var y -> x = y /\ ms = nil.
Proof.
  rewrite spine_spine'_rev=>/spine'_var[->/rev_nil->]//.
Qed.

Lemma lam_type_false Γ A B C s r t u l :
  Γ ⊢ Lam A B s r : C : t -> C <: u @ l -> False.
Proof.
  move e:(Lam A B s r)=>m ty.
  elim: ty A B s r u l e=>//{Γ m C t}.
  move=>Γ A B m s r t i k tyP ihP tym ihm A0 B0 s0 r0 u l e sb.
  solve_sub.
  move=>Γ A B m s i sb tym ihm tyB ihB A0 B0 s0 r u l e sb'; subst.
  apply: ihm; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma ind_type_false Γ X Cs A B C s r t u v x y l :
  Γ ⊢ Ind X Cs x : C : u -> C <: Pi A B s r t ->
  Γ ⊢ Ind X Cs x : v @ l : y -> False.
Proof.
  move e:(Ind X Cs x)=>m ty.
  elim: ty X Cs A B s r t v x y l e=>//{Γ m C u}.
  move=>Γ A Cs s l1 l2 k ar cCs tyA ihA tyCs X Cs0 A0 B s0 r t v x y l0
    [e1 e2 e3] sb tyI; subst.
  { inv ar. solve_sub.
    have[l3[l4[sb' _]]]:=ind_inv tyI.
    solve_sub. }
  move=>Γ A B m s i sb tym ihm _ _ X Cs A0 B0 s0 r t v x y l e sb' tym'; subst.
  { apply: ihm; eauto.
    apply: sub_trans; eauto. }
Qed.

Ltac solve_spine' :=
  match goal with
  | [ H : spine' _ ?ms = _ |- ?x ] =>
    destruct ms; simpl in H; intros;
    match goal with
    | [ H : _ = ?x |- _ ] => inv H
    end
  | [ H : _ = spine' _ ?ms |- ?x ] =>
    destruct ms; simpl in H; intros;
    match goal with
    | [ H : ?x = _ |- _ ] => inv H
    end
  end.

Ltac solve_spine :=
  match goal with
  | [ H : spine _ _ = _ |- _ ] =>
    rewrite spine_spine'_rev in H; solve_spine'
  | [ H : _ = spine _ _ |- _ ] =>
    rewrite spine_spine'_rev in H; solve_spine'
  end.

Lemma constr_respineU Γ I Cs A Q c C n s t l1 l2 :
  constr n U C ->
  arity U l1 A ->
  (I n = Ind A Cs U) ->
  [Γ] ⊢ I n : A : U ->
  [Γ] ⊢ Q : rearity U s (Ind A Cs U) A : U ->
  [Γ] ⊢ C.[I] : t @ l2 : U ->
  [Γ] ⊢ c : C.[I] : t ->
  exists l,
    let T := respine U s Q c C.[I] in
    [Γ] ⊢ T.2 : T.1 @ l : U.
Proof.
  elim: C Γ I Cs A Q c n s t l1 l2.
  all: try solve
      [intros;
       match goal with
       | [ H : constr _ _ _ |- _ ] =>
           inv H; exfalso; solve_spine
       end].
  move=>x Γ I Cs A Q c n s t l1 l2 cst ar e tyI tyQ tyv tyc.
  { inv cst.
    have[e1 e2]:=spine_var H; subst. inv ar.
    { exists l1=>//=. rewrite e=>//=.
      simpl in tyQ.
      simpl in tyc.
      simpl in tyv.
      rewrite e in tyc.
      rewrite e in tyv.
      have[_[_[/sub_sort_inv[e' _]_]]]:=ind_inv tyv; subst.
      replace (s @ l1) with (s @ l1).[c/] by autosubst.
      apply: clc_app; eauto.
      apply: (re_pure Γ).
      apply: merge_re_id; eauto. }
    { simpl in tyv.
      rewrite e in tyI.
      rewrite e in tyv.
      exfalso.
      apply: ind_type_false.
      apply: tyI.
      all: eauto. } }
  move=>A ihA B ihB s r t Γ I Cs A0 Q c n s0 t0 l1 l2 cst ar e tyI tyQ tyP tyc.
  { specialize
      (@ihB (A.[I] :{s} Γ) (up I)
            Cs..[up (ren (+1))] A0.[ren (+1)] Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) n.+1).
    inv cst; try solve[exfalso; solve_spine].
    { inv H5. simpl in tyP.
      have[l0[tyA[/sub_sort_inv[e0 _][_ tyB]]]]:=pi_inv tyP; subst.
      have e':(up I) n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U.
      { asimpl. rewrite e. by asimpl. }
      have ar':=arity_ren (+1) ar.
      have tyI': A.[I] :U [Γ] ⊢ up I n.+1 : A0.[ren (+1)] : U.
      { apply: eweakeningU; eauto. autosubst. }
      have tyQ':
        A.[I] :U [Γ] ⊢ Q.[ren (+1)]
          : rearity U s0 (Ind A0.[ren (+1)] Cs..[up (ren (+1))] U) A0.[ren (+1)] : U.
      { apply: eweakeningU; eauto. erewrite rearity_ren; eauto. }
      have tyc' : A.[I] :U [Γ] ⊢ c.[ren (+1)] : (Pi A B U U U).[I].[ren (+1)] : U.
      { apply: eweakeningU; eauto. }
      asimpl in tyc'.
      have tyv : A.[I] :U [Γ] ⊢ ids 0 : A.[I].[ren (+1)] : U.
      { apply: clc_var.
        constructor.
        apply: re_pure. }
      asimpl in tyv.
      have tyapp:=clc_app (re_pure (A.[I] :U Γ)) (merge_re_id _) tyc' tyv.
      asimpl in tyapp.
      have[l3 ty]:=ihB _ _ _ _ H9 ar' e' tyI' tyQ' tyB tyapp.
      exists (maxn l0 l3)=>//=.
      simpl in ty.
      remember (respine U s0 Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) B.[up I]) as h.
      destruct h=>//=.
      simpl in ty.
      apply: clc_pi_max; eauto=>//=.
      apply: re_pure.
      rewrite<-re_invo; eauto. }
    { inv H4. simpl in tyP.
      have[l0[tyA[/sub_sort_inv[e0 _][_ tyB]]]]:=pi_inv tyP; subst.
      have e':(up I) n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U.
      { asimpl. rewrite e. by asimpl. }
      have ar':=arity_ren (+1) ar.
      have tyI': A.[I] :U [Γ] ⊢ up I n.+1 : A0.[ren (+1)] : U.
      { apply: eweakeningU; eauto. autosubst. }
      have tyQ':
        A.[I] :U [Γ] ⊢ Q.[ren (+1)]
          : rearity U s0 (Ind A0.[ren (+1)] Cs..[up (ren (+1))] U) A0.[ren (+1)] : U.
      { apply: eweakeningU; eauto. erewrite rearity_ren; eauto. }
      have tyc' : A.[I] :U [Γ] ⊢ c.[ren (+1)] : (Pi A B U U U).[I].[ren (+1)] : U.
      { apply: eweakeningU; eauto. }
      asimpl in tyc'.
      have tyv : A.[I] :U [Γ] ⊢ ids 0 : A.[I].[ren (+1)] : U.
      { apply: clc_var.
        constructor.
        apply: re_pure. }
      asimpl in tyv.
      have tyapp:=clc_app (re_pure (A.[I] :U Γ)) (merge_re_id _) tyc' tyv.
      asimpl in tyapp.
      have[l3 ty]:=ihB _ _ _ _ H8 ar' e' tyI' tyQ' tyB tyapp.
      exists (maxn l0 l3)=>//=.
      simpl in ty.
      remember (respine U s0 Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) B.[up I]) as h.
      destruct h=>//=.
      simpl in ty.
      apply: clc_pi_max; eauto=>//=.
      apply: re_pure.
      rewrite<-re_invo; eauto. } }
  move=>m ihm n ihn Γ I Cs A Q c x s t l1 l2 cst ar e tyI tyQ tyapp tyc.
  { inv cst.
    rewrite<-H in tyapp.
    rewrite<-H in tyc.
    rewrite spine_subst.
    rewrite spine_subst in tyapp.
    rewrite spine_subst in tyc.
    asimpl.
    asimpl in tyapp.
    asimpl in tyc.
    rewrite e.
    rewrite e in tyapp.
    rewrite e in tyc.
    rewrite e in tyI.
    have[sp e']:=ind_spine_inv (re_pure _) ar tyapp; subst.
    have//={}sp:=rearity_spine s sp ar (sort_leqU U) (re_pure _) tyI.
    have spQ:=app_arity_spine tyQ sp (merge_re_id _).
    exists l1.
    pose proof (respine_spine_ind Q c A Cs U U s ms..[I]) as [->->]=>//=.
    replace (s @ l1) with (s @ l1).[c/] by autosubst.
    apply: clc_app.
    apply: (re_pure Γ).
    apply: merge_re_id.
    apply: spQ.
    apply: tyc. }
Qed.

Lemma constr_respineL Γ I Cs A Q c C n s s' t l1 l2 :
  constr n s C ->
  arity s l1 A ->
  (I n = Ind A Cs s) ->
  [Γ] ⊢ I n : A : U ->
  [Γ] ⊢ Q : rearity L s' (Ind A Cs s) A : U ->
  [Γ] ⊢ C.[I] : t @ l2 : U ->
  exists l,
    let T := respine L s' Q c C.[I] in
    [Γ] ⊢ T.2 : T.1 @ l : U.
Proof.
  elim: C Γ I Cs A Q c n s s' t l1 l2.
  all: try solve
      [intros;
       match goal with
       | [ H : constr _ _ _ |- _ ] =>
           inv H; exfalso; solve_spine
       end].
  move=>x Γ I Cs A Q c n s s' t l1 l2 cst ar e tyI tyQ tyv.
  { inv cst.
    have[e1 e2]:=spine_var H; subst. inv ar.
    { exists l1=>//=. rewrite e=>//=. }
    { simpl in tyv.
      rewrite e in tyI.
      rewrite e in tyv.
      exfalso.
      apply: ind_type_false.
      apply: tyI.
      all: eauto. } }
  move=>A ihA B ihB s r t Γ I Cs A0 Q c n s0 s' t0 l1 l2 cst ar e tyI tyQ tyP.
  { specialize
      (@ihB (A.[I] :{s} Γ) (up I)
            Cs..[up (ren (+1))] A0.[ren (+1)] Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) n.+1).
    inv cst; try solve[exfalso; solve_spine].
    { simpl in tyP.
      have[l0[tyA[/sub_sort_inv[e0 _][_ tyB]]]]:=pi_inv tyP; subst.
      have e':(up I) n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] t0.
      { asimpl. rewrite e. by asimpl. }
      have ar':=arity_ren (+1) ar.
      have tyI': [A.[I] :{s} Γ] ⊢ up I n.+1 : A0.[ren (+1)] : U.
      { destruct s=>//=.
        apply: eweakeningU; eauto. autosubst.
        apply: eweakeningN; eauto. autosubst. }
      have tyQ':
        [A.[I] :{s} Γ] ⊢ Q.[ren (+1)]
          : rearity L s' (Ind A0.[ren (+1)] Cs..[up (ren (+1))] t0) A0.[ren (+1)] : U.
      { destruct s=>//=.
        apply: eweakeningU; eauto. erewrite rearity_ren; eauto.
        apply: eweakeningN; eauto. erewrite rearity_ren; eauto. }
      have[l3 ty]:=ihB _ _ _ _ _ H9 ar' e' tyI' tyQ' tyB.
      exists (maxn l0 l3)=>//=.
      simpl in ty.
      remember (respine L s' Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) B.[up I]) as h.
      destruct h=>//=.
      simpl in ty.
      apply: clc_pi_max; eauto=>//=.
      apply: re_pure.
      destruct s.
      rewrite<-re_invo; eauto.
      rewrite<-re_invo; eauto. }
    { simpl in tyP.
      have[l0[tyA[/sub_sort_inv[e0 _][_ tyB]]]]:=pi_inv tyP; subst.
      have e':(up I) n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] t0.
      { asimpl. rewrite e. by asimpl. }
      have ar':=arity_ren (+1) ar.
      have tyI': [A.[I] :{s} Γ] ⊢ up I n.+1 : A0.[ren (+1)] : U.
      { destruct s=>//=.
        apply: eweakeningU; eauto. autosubst.
        apply: eweakeningN; eauto. autosubst. }
      have tyQ':
        [A.[I] :{s} Γ] ⊢ Q.[ren (+1)]
          : rearity L s' (Ind A0.[ren (+1)] Cs..[up (ren (+1))] t0) A0.[ren (+1)] : U.
      { destruct s=>//=.
        apply: eweakeningU; eauto. erewrite rearity_ren; eauto.
        apply: eweakeningN; eauto. erewrite rearity_ren; eauto. }
      have[l3 ty]:=ihB _ _ _ _ _ H8 ar' e' tyI' tyQ' tyB.
      exists (maxn l0 l3)=>//=.
      simpl in ty.
      remember (respine L s' Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) B.[up I]) as h.
      destruct h=>//=.
      simpl in ty.
      apply: clc_pi_max; eauto=>//=.
      apply: re_pure.
      destruct s.
      rewrite<-re_invo; eauto.
      rewrite<-re_invo; eauto. } }
  move=>m ihm n ihn Γ I Cs A Q c x s s' t l1 l2 cst ar e tyI tyQ tyapp.
  { inv cst.
    rewrite<-H in tyapp.
    rewrite spine_subst.
    rewrite spine_subst in tyapp.
    asimpl.
    asimpl in tyapp.
    rewrite e.
    rewrite e in tyapp.
    rewrite e in tyI.
    have[sp e']:=ind_spine_inv (re_pure _) ar tyapp; subst.
    have leq: t ≤ L.
    { destruct t; constructor. }
    have//={}sp:=rearity_spine s' sp ar leq (re_pure _) tyI.
    have spQ:=app_arity_spine tyQ sp (merge_re_id _).
    exists l1.
    pose proof (respine_spine_ind Q c A Cs L t s' ms..[I]) as [->->]=>//=. }
Qed.
