From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_arity_spine
  clc_validity clc_typing_spine clc_respine clc_iota_lemma
  clc_soundness clc_resolution clc_resolve_spine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive eval : context term -> term -> context term -> term -> Prop :=
| eval_sort Θ s i l :
  l = size Θ ->
  eval Θ (s @ i) (s @ i :U Θ) (Ptr l)
| eval_pi Θ A B s r t l :
  l = size Θ ->
  eval Θ (Pi A B s r t) (Pi A B s r t :U Θ) (Ptr l)
| eval_lam Θ A m s t l :
  l = size Θ ->
  eval Θ (Lam A m s t) (Lam A m s t :{t} Θ) (Ptr l)
| eval_appL Θ Θ' m m' n :
  eval Θ m Θ' m' ->
  eval Θ (App m n) Θ' (App m' n)
| eval_appR Θ Θ' l n n' :
  eval Θ n Θ' n' ->
  eval Θ (App (Ptr l) n) Θ' (App (Ptr l) n')
| eval_beta Θ Θ' l1 l2 A m s t :
  lookup Θ l1 (Lam A m s t) Θ' ->
  eval Θ (App (Ptr l1) (Ptr l2)) Θ' m.[Ptr l2/]
| eval_indd Θ l A Cs s :
  l = size Θ ->
  eval Θ (Ind A Cs s) (Ind A Cs s :U Θ) (Ptr l)
| eval_appI Θ Θ' l1 l2 l A Cs s ms :
  l = size Θ ->
  lookup Θ l1 (spine (Ind A Cs s) ms) Θ' ->
  eval 
    Θ (App (Ptr l1) (Ptr l2)) 
    (spine (Ind A Cs s) (rcons ms (Ptr l2)) :U Θ') (Ptr l)
| eval_constr Θ l i I s :
  l = size Θ ->
  eval Θ (Constr i I s) (Constr i I s :{s} Θ) (Ptr l)
| eval_appC Θ Θ' l1 l2 l i I s ms :
  l = size Θ ->
  lookup Θ l1 (spine (Constr i I s) ms) Θ' ->
  eval
    Θ (App (Ptr l1) (Ptr l2))
    (spine (Constr i I s) (rcons ms (Ptr l2)) :{s} Θ') (Ptr l)
| eval_case Θ Θ' m m' Q Fs :
  eval Θ m Θ' m' ->
  eval Θ (Case m Q Fs) Θ' (Case m' Q Fs)
| eval_iota1 Θ Θ' l i I s ms Q Fs F :
  iget i Fs F ->
  lookup Θ l (spine (Constr i I s) ms) Θ' ->
  eval Θ (Case (Ptr l) Q Fs) Θ' (spine F ms)
| eval_fix1 Θ l k A m :
  l = size Θ ->
  eval Θ (Fix k A m) (Fix k A m :U Θ) (Ptr l)
| eval_fix2 Θ Θ1 Θ2 l k A m ms n n' :
  1 <= size ms ->
  size ms <= k ->
  all_ptr ms ->
  lookup Θ l (Fix k A m) Θ1 ->
  eval Θ1 n Θ2 n' ->
  eval Θ (spine (Ptr l) (rcons ms n)) Θ2 (spine (Ptr l) (rcons ms n'))
| eval_iota2 Θ Θ1 Θ2 i l l1 l2 k A I m ms ns s :
  k = size ms ->
  l = size Θ ->
  all_ptr ms ->
  lookup Θ l1 (Fix k A m) Θ1 ->
  lookup Θ1 l2 (spine (Constr i I s) ns) Θ2 ->
  eval
    Θ (spine (Ptr l1) (rcons ms (Ptr l2)))
    ((spine (Constr i I s) ns) :{s} Θ2) (spine m.[Ptr l1/] (rcons ms (Ptr l))).

Inductive agree_resolve :
  context term -> context term -> 
  (var -> term) -> (var -> term) -> nat -> Prop :=
| agree_resolve_nil Θ :
  Θ |> U ->
  wr_heap Θ ->
  agree_resolve nil Θ ids ids 0
| agree_resolve_upTy Γ Θ σ σ' A x s :
  agree_resolve Γ Θ σ σ' x ->
  agree_resolve (A :{s} Γ) Θ (up σ) (up σ') x.+1
| agree_resolve_upN Γ Θ σ σ' x :
  agree_resolve Γ Θ σ σ' x ->
  agree_resolve (_: Γ) Θ (up σ) (up σ') x.+1
| agree_resolve_wkU Γ Θ1 Θ2 Θ σ σ' m m' A :
  Θ1 ∘ Θ2 => Θ ->
  Θ2 |> U ->
  wr_heap Θ2 ->
  resolve Θ2 m m' ->
  agree_resolve Γ Θ1 σ σ' 0 ->
  agree_resolve (A :U Γ) Θ (m .: σ) (m' .: σ') 0
| agree_resolve_wkL Γ Θ1 Θ2 Θ σ σ' m m' A :
  Θ1 ∘ Θ2 => Θ ->
  wr_heap Θ2 ->
  resolve Θ2 m m' ->
  agree_resolve Γ Θ1 σ σ' 0 ->
  agree_resolve (A :L Γ) Θ (m .: σ) (m' .: σ') 0
| agree_resolve_wkN Γ Θ σ σ' m m' :
  agree_resolve Γ Θ σ σ' 0 ->
  agree_resolve (_: Γ) Θ (m .: σ) (m' .: σ') 0.

Lemma agree_resolve_key Γ Θ σ σ' x s :
  agree_resolve Γ Θ σ σ' x -> Γ |> s -> Θ |> s.
Proof.
  elim=>//{Γ Θ σ σ' x}.
  move=>Θ k1 wr k2. destruct s; eauto. apply: key_impure.
  move=>Γ Θ σ σ' A x t agr ih k. inv k; eauto.
  move=>Γ Θ σ σ' x agr ih k. inv k; eauto.
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k1 wr rsm agr ih k2. inv k2.
    apply: merge_pure_pure; eauto.
    apply: key_impure.
  move=>Γ Θ1 Θ2 Θ σ1 σ2 m m' A mrg wr rsm agr ih k. inv k.
    apply: key_impure.
  move=>Γ Θ σ1 σ2 m m' agr ih k. inv k; eauto.
Qed.

Lemma nf_agree_resolve_var Γ Θ σ σ' i x :
  agree_resolve Γ Θ σ σ' i -> x < i -> Var x = σ x.
Proof.
  move=>agr. elim: agr x=>//{Γ Θ σ σ' i}.
  move=>Γ Θ σ σ' A x s agr ih [|i] le//.
  asimpl.
  have/ih<-//:i < x by eauto.
  move=>Γ Θ σ σ' x agr ih [|i] le//.
  asimpl.
  have/ih<-//:i < x by eauto.
Qed.

Lemma nf_agree_resolve Γ Θ σ σ' i j m :
  nf i m -> i <= j -> agree_resolve Γ Θ σ σ' j -> m = m.[σ].
Proof with eauto using agree_resolve.
  move=>nf. move: i m nf Γ Θ σ σ' j.
  apply: nf_ind_nested...
  move=>i x lt Γ Θ σ σ' j leq agr.
  { apply: nf_agree_resolve_var; eauto.
    apply: leq_trans; eauto. }
  move=>i A B s r t nfA ihA nfB ihB Γ Θ σ σ' j leq agr.
  { have lt : i < j.+1 by eauto. asimpl. f_equal.
    apply: ihA. exact: leq. exact: agr.
    apply: ihB. exact: lt.
    apply: agree_resolve_upN. exact: agr. }
  move=>i A m s t nfA ihA nfm ihm Γ Θ σ σ' j leq agr.
  { have lt : i < j.+1 by eauto. asimpl. f_equal.
    apply: ihA. exact: leq. exact: agr.
    apply: ihm. exact: lt.
    apply: agree_resolve_upN. exact: agr. }
  move=>i m n nfm ihm nfn ihn Γ Θ σ σ' j leq agr.
  { asimpl. f_equal.
    apply: ihm; eauto.
    apply: ihn; eauto. }
  move=>i A Cs s nfA ihA nfCs ihCs Γ Θ σ σ' j leq agr.
  { asimpl. f_equal.
    apply: ihA; eauto.
    elim: ihCs=>{Cs nfCs}...
    move=>C Cs hd ih tl.
    asimpl. f_equal...
    have lt : i < j.+1 by eauto.
    apply: hd. exact: lt.
    apply: agree_resolve_upN. exact: agr. }
  move=>i x I s nfI ihI Γ Θ σ σ' j leq agr.
  { asimpl. f_equal.
    apply: ihI; eauto. }
  move=>i m Q Fs nfm ihm nfQ ihQ nfFs ihFs Γ Θ σ σ' j leq agr.
  { asimpl. f_equal.
    apply: ihm; eauto.
    apply: ihQ; eauto.
    elim: ihFs=>{Fs nfFs}...
    move=>F Fs hd ih tl.
    asimpl. f_equal... }
  move=>i k A m nfA ihA nfm ihm Γ Θ σ σ' j leq agr.
  { have lt : i < j.+1 by eauto. asimpl. f_equal.
    apply: ihA; eauto.
    apply: ihm. exact: lt.
    apply: agree_resolve_upN. exact: agr. }
Qed.

Lemma agree_resolve_wr Γ Θ σ σ' x :
  agree_resolve Γ Θ σ σ' x -> wr_heap Θ.
Proof with eauto using wr_heap.
  elim=>{Γ Θ σ σ' x}...
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k wr2 rsm agr wr1.
  apply: wr_merge; eauto.
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg wr2 rsm agr wr1.
  apply: wr_merge; eauto.
Qed.

Definition id_ren i ξ := forall x, x < i -> ξ x = x.

Lemma id_ren1 : id_ren 0 (+1).
Proof. move=>x h. inv h. Qed.

Lemma id_ren_up i ξ : id_ren i ξ -> id_ren i.+1 (upren ξ).
Proof.
  move=>idr x h.
  destruct x.
  asimpl. eauto.
  asimpl. rewrite idr; eauto.
Qed.

Lemma nf_id_ren i m ξ : nf i m -> id_ren i ξ -> m = m.[ren ξ].
Proof.
  move=>nf. move: i m nf ξ.
  apply: nf_ind_nested=>//.
  move=>i x lt ξ idr.
  { asimpl. rewrite idr; eauto. }
  move=>i A B s r t nfA ihA nfB ihB ξ idr.
  { asimpl.
    rewrite<-ihA; eauto.
    rewrite<-ihB; eauto.
    apply: id_ren_up; eauto. }
  move=>i A m s t nfA ihA nfm ihm ξ idr.
  { asimpl.
    rewrite<-ihA; eauto.
    rewrite<-ihm; eauto.
    apply: id_ren_up; eauto. }
  move=>i m n nfm ihm nfn ihn ξ idr.
  { asimpl.
    rewrite<-ihm; eauto.
    rewrite<-ihn; eauto. }
  move=>i A Cs s nfA ihA nfCs ihCs ξ idr.
  { asimpl. f_equal.
    rewrite<-ihA; eauto.
    elim: ihCs=>//{Cs nfCs}.
    move=>C Cs ih hd tl.
    asimpl. f_equal; eauto.
    apply: ih.
    apply: id_ren_up; eauto. }
  move=>i x I s nfI ihI ξ idr.
  { asimpl. f_equal.
    rewrite<-ihI; eauto. }
  move=>i m Q Fs nfm ihm nfQ ihQ nfFs ihFs ξ idr.
  { asimpl. f_equal.
    rewrite<-ihm; eauto.
    rewrite<-ihQ; eauto.
    elim: ihFs=>//{Fs nfFs}.
    move=>F Fs ih hd tl.
    asimpl. f_equal; eauto. }
  move=>i k A m nfA ihA nfm ihm ξ idr.
  { asimpl.
    rewrite<-ihA; eauto.
    rewrite<-ihm; eauto.
    apply: id_ren_up; eauto. }
Qed.

Lemma ind_head_ren_inv m ξ : ind_head m.[ren ξ] -> ind_head m.
Proof.
  elim: m ξ=>//.
  move=>x ξ h. inv h. exfalso. solve_spine.
  move=>A ihA B ihB s r t ξ h. inv h. exfalso. solve_spine.
  move=>A ihA m ihm s t ξ h. inv h. exfalso. solve_spine.
  move=>m ihm n ihn ξ h. inv h. 
  { have[ms'[e1 e2]]:=ind_spine_app_inv H0; subst.
    have/ihm{}ihm: ind_head m.[ren ξ].
    { rewrite<-e1.
      constructor. }
    inv ihm.
    rewrite spine_app_rcons.
    constructor. }
  move=>A ihA Cs s ξ h.
  { replace (Ind A Cs s) with (spine (Ind A Cs s) nil) by eauto.
    constructor. }
  move=>i m ihm s ξ h. inv h. exfalso. solve_spine.
  move=>m ihm Q ihQ Fs ξ h. inv h. exfalso. solve_spine.
  move=>k A ihA m ihm ξ h. inv h. exfalso. solve_spine.
Qed.

Lemma resolve_ren Θ m m' i ξ :
  resolve Θ m m' -> wr_heap Θ ->
  id_ren i ξ -> resolve Θ m.[ren ξ] m'.[ren ξ].
Proof with eauto using resolve, All2.
  move=>rs. move: Θ m m' rs i ξ.
  apply: resolve_ind_nested...
  move=>Θ A A' B B' s r t k rsA ihA rsB ihB i ξ wr idr.
  { asimpl.
    econstructor...
    apply: ihB...
    apply: id_ren_up... }
  move=>Θ A A' m m' s t k rsA ihA rsm ihm i ξ wr idr.
  { asimpl.
    econstructor...
    apply: ihA...
    apply: wr_heap_re...
    apply: ihm...
    apply: id_ren_up... }
  move=>Θ1 Θ2 Θ m m' n n' mrg rm ihm rn ihn i ξ wr idr.
  { asimpl.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    econstructor... }
  move=>Θ A A' Cs Cs' s k rA ihA rCs ihCs i ξ wr idr.
  { asimpl.
    econstructor...
    elim: ihCs=>{Cs Cs' rCs}...
    move=>C C' Cs Cs' ih hd tl.
    asimpl.
    constructor...
    apply: ih...
    apply: id_ren_up... }
  move=>Θ1 Θ2 Θ m m' Q Q' Fs Fs' mrg rm ihm rQ ihQ rFs ihFs i ξ wr idr.
  { asimpl.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    econstructor...
    apply: ihQ...
    apply: wr_heap_re...
    elim: ihFs=>{Fs Fs' rFs}... }
  move=>Θ k0 A A' m m' k rA ihA rm ihm i ξ wr idr.
  { asimpl.
    econstructor...
    apply: ihm...
    apply: id_ren_up... }
  move=>Θ Θ' l m m' fr rm ihm i ξ wr idr.
  { asimpl.
    have nf0:=lookup_wr_nf fr wr.
    have {}wr:=lookup_wr fr wr.
    have nf0':=resolve_wr_nfi' rm wr nf0.
    have leq : 0 <= i by eauto.
    have nfi:=nf_weaken nf0' leq.
    have<-:=nf_id_ren nfi idr.
    econstructor... }
Qed.

Lemma agree_resolve_id Γ Θ σ σ' x i s A :
  agree_resolve Γ Θ σ σ' i -> has Γ x s A -> resolve Θ (σ x) (σ' x).
Proof with eauto using resolve.
  move=>agr. elim: agr x s A=>{Γ Θ σ σ' i}.
  move=>Θ k wr x s A hs. inv hs.
  move=>Γ Θ σ σ' A x s agr ih y t B hs.
  { inv hs; asimpl.
    constructor.
    apply: agree_resolve_key...
    apply: resolve_ren...
    apply: agree_resolve_wr...
    apply: id_ren1. }
  move=>Γ Θ σ σ' x agr ih y s A hs.
  { inv hs; asimpl.
    apply: resolve_ren...
    apply: agree_resolve_wr...
    apply: id_ren1. }
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k2 wr rsm agr ih x s B hs.
  { inv hs; asimpl.
    have k1:=agree_resolve_key agr H5.
    have[e1 e2]:=merge_pure_eq mrg k1 k2.
    subst...
    have->:=merge_pureR mrg k2... }
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg wr rsm agr ih x s B hs.
  { inv hs; asimpl.
    have k:=agree_resolve_key agr H5.
    have->:=merge_pureL mrg k... }
  move=>Γ Θ σ σ' m m' agr ih x s A hs.
  { inv hs; asimpl; eauto. }
Qed.

Lemma agree_resolve_re Γ Θ σ σ' x :
  agree_resolve Γ Θ σ σ' x -> agree_resolve [Γ] [Θ] σ σ' x.
Proof with eauto using agree_resolve.
  elim=>//={Γ Θ σ σ' x}...
  move=>Θ k wr. 
  { constructor. 
    apply: re_pure.
    apply: wr_heap_re... }
  move=>Γ Θ σ σ' A x [|]/= agr1 agr2...
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k wr rsm agr1 agr2.
  { econstructor.
    apply: merge_re3...
    apply: re_pure.
    apply: wr_heap_re...
    rewrite<-pure_re; eauto.
    exact: agr2. }
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg wr rsm agr1 agr2.
  { have[e1[e2 e3]]:=merge_re_re mrg.
    econstructor.
    rewrite<-e2=>//. }
Qed.

Lemma agree_resolve_merge_inv Γ1 Γ2 Γ Θ σ σ' x :
  agree_resolve Γ Θ σ σ' x ->
  Γ1 ∘ Γ2 => Γ ->
  exists Θ1 Θ2,
    Θ1 ∘ Θ2 => Θ /\
    agree_resolve Γ1 Θ1 σ σ' x /\
    agree_resolve Γ2 Θ2 σ σ' x.
Proof with eauto using merge, agree_resolve.
  move=>agr. elim: agr Γ1 Γ2=>{Γ Θ σ σ' x}.
  move=>Θ k wr Γ1 Γ2 mrg.
  { inv mrg. 
    have[G1[G2[k1[k2 mrg]]]]:=pure_split k.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    exists G1. exists G2... }
  move=>Γ Θ σ σ' A x s agr ih Γ1 Γ2 mrg.
  { destruct s; inv mrg.
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists D1. exists D2...
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists D1. exists D2...
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists D1. exists D2... }
  move=>Γ Θ σ σ' x agr ih Γ1 Γ2 mrg.
  { inv mrg.
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists D1. exists D2... }
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg1 k wr rsm agr ih Γ1 Γ2 mrg2.
  { inv mrg2.
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    have e:=merge_pureR mrg1 k; subst.
    have mrgr:=merge_re_id Θ2.
    rewrite<-pure_re in mrgr...
    have[G1[G2[mrg3[mrg4 mrg5]]]]:=merge_distr mrg1 mrg' mrgr.
    exists G1. exists G2.
    repeat split... }
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg1 wr rsm agr ih Γ1 Γ2 mrg2.
  { inv mrg2.
    { have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      have[G[mrg3 mrg4]]:=merge_splitL mrg1 mrg'.
      exists G. exists D2.
      repeat split... } 
    { have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      have[G[mrg3 mrg4]]:=merge_splitR mrg1 mrg'.
      exists D1. exists G.
      repeat split... } }
  move=>Γ Θ σ σ' m m' agr ih Γ1 Γ2 mrg.
  { inv mrg.
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists D1. exists D2.
    repeat split... }
Qed.

Lemma All2i_resolve_subst Γ Θ1 Θ2 Θ Fs1 Fs2 Cs s x i σ σ' :
  All2 (resolve Θ1) Fs1 Fs2 ->
  Θ1 ∘ Θ2 => Θ ->
  All2i
    (fun _ F C =>
      constr 0 s C /\
      forall Θ1 Θ2 Θ m σ σ' x,
        Θ1 ∘ Θ2 => Θ ->
        resolve Θ1 m F ->
        wr_heap Θ1 ->
        agree_resolve Γ Θ2 σ σ' x ->
        resolve Θ m.[σ] F.[σ']) 
    i Fs2 Cs ->
  wr_heap Θ1 ->
  agree_resolve Γ Θ2 σ σ' x ->
  All2 (resolve Θ) Fs1..[σ] Fs2..[σ'].
Proof with eauto using All2.
  move=>h. elim: h Γ Θ2 Θ Cs s x i σ σ'=>{Fs1 Fs2}...
  move=>F1 F2 Fs1 Fs2 rF rFs ih1 Γ Θ2 Θ Cs s x i σ σ' mrg hd wr agr.
  inv hd.
  move:H2=>[_ ih2].
  asimpl.
  constructor...
Qed.

Lemma resolve_subst Γ Θ1 Θ2 Θ m m' A r σ σ' x :
  Γ ⊢ m' : A : r -> Θ1 ∘ Θ2 => Θ ->
  resolve Θ1 m m' -> wr_heap Θ1 ->
  agree_resolve Γ Θ2 σ σ' x ->
  resolve Θ m.[σ] m'.[σ'].
Proof with eauto using resolve, merge_pure_pure, All2.
  move=>ty. move: Γ m' A r ty Θ1 Θ2 Θ m σ σ' x.
  apply: clc_type_ind_nested...
  move=>Γ s l k Θ1 Θ2 Θ m σ σ' x mrg rsm wr agr.
  { inv rsm; asimpl.
    { have k2:=agree_resolve_key agr k.
      econstructor... }
    { inv H0.
      have e:=lookup_wr_sort H wr; subst.
      have p:=agree_resolve_key agr k.
      have [e1 e2]:=merge_pure_eq mrg H4 p; subst.
      econstructor...
      exfalso. apply: lookup_wr_ptr; eauto. } }
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ1 Θ2 Θ m σ σ' x mrg rsm wr agr.
  { inv rsm; asimpl.
    { constructor.
      have k2:=agree_resolve_key agr k...
      apply: ihA...
      have ag1:agree_resolve (A :U [Γ]) Θ2 (up σ) (up σ') x.+1. 
      { apply: agree_resolve_upTy; eauto.
        rewrite<-pure_re; eauto. }
      have ag2:agree_resolve (_: [Γ]) Θ2 (up σ) (up σ') x.+1.
      { apply: agree_resolve_upN.
        rewrite<-pure_re; eauto. } 
      apply: ihB...
      destruct s... }
    { inv H0.
      have nfP:=lookup_wr_nf H wr.
      have e:=lookup_wr_pi H wr; subst.
      have k1:=agree_resolve_key agr k.
      have[e1 e2]:=merge_pure_eq mrg H6 k1; subst.
      inv nfP.
      econstructor...
      econstructor...
      have le1:0 <= x by eauto.
      have->:=nf_agree_resolve H3 le1 agr.
      apply: ihA...
      have le2:0 < x.+1 by eauto.
      destruct s.
      { have agr': agree_resolve (A :U [Γ]) Θ (up σ) (up σ') x.+1.
        apply: agree_resolve_upTy.
        rewrite<-pure_re...
        have->:=nf_agree_resolve H8 le2 agr'... }
      { have agr': agree_resolve (_: [Γ]) Θ (up σ) (up σ') x.+1.
        apply: agree_resolve_upN.
        rewrite<-pure_re...
        have->:=nf_agree_resolve H8 le2 agr'... }
      exfalso. apply: lookup_wr_ptr; eauto. } }
  move=>Γ x A s hs Θ1 Θ2 Θ m σ σ' x0 mrg rsm wr agr.
  { inv rsm; asimpl.
    { have e:=merge_pureL mrg H2; subst.
      apply: agree_resolve_id... }
    { inv H0.
      have//:=lookup_wr_var H wr.
      have//:=lookup_wr_ptr H wr. } }
  move=>Γ A B m s r t i k tyP ihP tym ihm Θ1 Θ2 Θ n σ σ' x mrg rsL wr agr.
  { have[lP[tyA[_[_ tyB]]]]:=pi_inv tyP.
    inv rsL; asimpl.
    { econstructor.
      destruct t.
      have k2:=agree_resolve_key agr k...
      apply: key_impure.
      have rsP: resolve [Θ1] (Pi A0 B s r t) (Pi A B s r t).
      { econstructor...
        apply: re_pure.
        apply: resolve_type_refl... }
      have{}ihP:=ihP _ _ _ _ _ _ _ 
        (merge_re3 mrg) rsP (wr_heap_re wr) (agree_resolve_re agr).
      inv ihP...
      apply: ihm...
      destruct s.
      { econstructor... }
      { econstructor... } }
    { inv H0.
      have nfL:=lookup_wr_nf H wr.
      have k2:=agree_resolve_key agr k.
      inv nfL.
      have[G[fr mrg']]:=lookup_merge H mrg.
      have wr':=lookup_wr H wr.
      econstructor...
      econstructor...
      apply: merge_key...
      have le1:0 <= x by eauto.
      have->:=nf_agree_resolve H3 le1 agr.
      have[e1[e2 e3]]:=merge_re_re mrg'.
      have rsP: resolve [Θ'] (Pi A0 B s r t) (Pi A B s r t).
      { econstructor...
        apply: re_pure.
        apply: resolve_type_refl... }
      have{}ihP:=ihP _ _ _ _ _ _ _ 
        (merge_re3 mrg') rsP (wr_heap_re wr') (agree_resolve_re agr).
      inv ihP...
      have le2:0 < x.+1 by eauto.
      destruct s.
      { have agr': agree_resolve (A :U Γ) Θ2 (up σ) (up σ') x.+1.
          apply: agree_resolve_upTy...
        have->:=nf_agree_resolve H7 le2 agr'... }
      { have agr': agree_resolve (A :L Γ) Θ2 (up σ) (up σ') x.+1.
          apply: agree_resolve_upTy...
        have->:=nf_agree_resolve H7 le2 agr'... }
      exfalso. apply: lookup_wr_ptr; eauto. } }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg1 tym ihm tyn ihn 
    Θ1 Θ2 Θ m0 σ σ' x mrg2 rsm wr agr.
  { inv rsm; asimpl.
    { have[wr1 wr2]:=wr_merge_inv H1 wr.
      have[G1[G2[mrg5[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[D1[D2[mrg6[mrg7 mrg8]]]]:=merge_distr mrg2 H1 mrg5.
      econstructor... }
    { inv H0.
      have nfa:=lookup_wr_nf H wr.
      inv nfa.
      have[G[fr mrg']]:=lookup_merge H mrg2.
      have[G1[G2[mrg5[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[D1[D2[mrg6[mrg7 mrg8]]]]:=merge_distr mrg' H3 mrg5.
      have wr':=lookup_wr H wr.
      have[wr1 wr2]:=wr_merge_inv H3 wr'.
      have le:0 <= x by eauto.
      econstructor...
      econstructor.
      apply: mrg6.
      have->:=nf_agree_resolve H4 le agr1. apply:ihm...
      have->:=nf_agree_resolve H5 le agr2. apply:ihn...
      exfalso. apply: lookup_wr_ptr; eauto. } }
  move=>Γ A Cs s l1 l2 k ar cCs tyA ihA tyCs ihCs Θ1 Θ2 Θ m σ σ' x mrg rsm wr agr.
  { inv rsm; asimpl.
    { have k2:=agree_resolve_key agr k.
      econstructor...
      elim: H6 ihCs...
      move=>C1 C2 Cs1 Cs2 rC rCs ih tl. inv tl.
      asimpl. constructor...
      apply: H1...
      apply: agree_resolve_upTy... }
    { inv H0.
      have nfI:=lookup_wr_nf H wr.
      have fr:lookup Θ1 l (spine (Ind A0 Cs0 s) nil) Θ' by eauto.
      have e:=lookup_wr_ind fr wr; subst.
      have k2:=agree_resolve_key agr k.
      have[e1 e2]:=merge_pure_eq mrg H6 k2; subst.
      inv nfI.
      econstructor...
      econstructor...
      have leq:0 <= x by eauto.
      have->:=nf_agree_resolve H3 leq agr.
      apply: ihA...
      have lt:0 < x.+1 by eauto.
      have agr': agree_resolve (A :U Γ) Θ (up σ) (up σ') x.+1.
        apply: agree_resolve_upTy...
      elim: H8 H5 ihCs...
      move=>C1 C2 Cs1 Cs2 rC rCs ih hd tl. 
      inv hd. inv tl.
      constructor...
      have->:=nf_agree_resolve H2 lt agr'.
      apply: H5...
      exfalso. apply: lookup_wr_ptr... } }
  move=>Γ A s i C Cs//=k ig tyI ihI Θ1 Θ2 Θ m σ σ' x mrg rsm wr agr.
  { inv rsm; asimpl.
    { have k2:=agree_resolve_key agr k.
      econstructor... }
    { inv H0.
      have nfC:=lookup_wr_nf H wr.
      have k2:=agree_resolve_key agr k.
      have e:=merge_pureR mrg k2; subst.
      econstructor...
      econstructor...
      inv nfC.
      have leq:0 <= x by eauto.
      have->:=nf_agree_resolve H2 leq agr.
      apply: ihI...
      have[G[_ mrg1]]:=lookup_merge H mrg.
      have e:=merge_pureR mrg1 k2; subst=>//.
      apply: lookup_wr...
      exfalso. apply: lookup_wr_ptr... } }
  move=>Γ1 Γ2 Γ A Q s s' l k Fs Cs m ms//=leq ar key mrg1 
    tym ihm tyQ ihQ tyFs ihFs Θ1 Θ2 Θ m0 σ σ' x mrg2 rsm wr agr.
  { inv rsm; asimpl.
    { have[wr1 wr2]:=wr_merge_inv H2 wr.
      have[G1[G2[mrg3[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[G3[G4[mrg4[mrg5 mrg6]]]]:=merge_distr mrg2 H2 mrg3.
      have[e1[e2 _]]:=merge_re_re mrg6.
      econstructor.
      apply: mrg4.
      apply: ihm...
      apply: ihQ...
      rewrite<-e2.
      apply: merge_re_id.
      apply: wr_heap_re...
      rewrite e1.
      apply: agree_resolve_re...
      apply: All2i_resolve_subst... }
    { inv H0.
      have v:=wr_lookup_value H wr. inv v.
      exfalso. solve_spine.
      exfalso. solve_spine.
      exfalso. apply: lookup_wr_ptr... } }
  move=>Γ k0 A m l k tyA ihA tym ihm Θ1 Θ2 Θ m0 σ σ' x mrg rsm wr agr.
  { inv rsm; asimpl.
    { have k2:=agree_resolve_key agr k.
      econstructor...
      apply: ihm...
      apply: agree_resolve_upTy... }
    { inv H0.
      have nfF:=lookup_wr_nf H wr.
      inv nfF.
      have e:=lookup_wr_fix H wr; subst.
      have k2:=agree_resolve_key agr k.
      have e:=merge_pureR mrg k2; subst.
      have leq: 0 <= x by eauto.
      have lt: 0 < x.+1 by eauto.
      econstructor...
      econstructor...
      have->:=nf_agree_resolve H3 leq agr.
      apply: ihA...
      have agr': agree_resolve (A :U Γ) Θ2 (up σ) (up σ') x.+1.
      { apply: agree_resolve_upTy... }
      have->:=nf_agree_resolve H5 lt agr'.
      apply: ihm...
      exfalso. apply: lookup_wr_ptr... } }
Qed.

Lemma resolve_substU Θ1 Θ2 Θ m m' n n' A B r :
  A :U nil ⊢ m' : B : r -> Θ2 |> U ->
  resolve Θ1 m m' -> resolve Θ2 n n' -> wr_heap Θ ->
  Θ1 ∘ Θ2 => Θ -> resolve Θ m.[n/] m'.[n'/].
Proof.
  move=>ty k rsm rsn wr mrg.
  have[wr1 wr2]:=wr_merge_inv mrg wr.
  have mrg':=merge_reL Θ2.
  apply: resolve_subst.
  exact: ty.
  exact: mrg.
  exact: rsm.
  exact: wr1.
  econstructor; eauto.
  econstructor.
  apply: re_pure.
  apply: wr_heap_re; eauto.
Qed.

Lemma resolve_substL Θ1 Θ2 Θ m m' n n' A B r :
  A :L nil ⊢ m' : B : r -> 
  resolve Θ1 m m' -> resolve Θ2 n n' -> wr_heap Θ ->
  Θ1 ∘ Θ2 => Θ -> resolve Θ m.[n/] m'.[n'/].
Proof.
  move=>ty rsm rsn wr mrg.
  have[wr1 wr2]:=wr_merge_inv mrg wr.
  have mrg':=merge_reL Θ2.
  apply: resolve_subst.
  exact: ty.
  exact: mrg.
  exact: rsm.
  exact: wr1.
  econstructor; eauto.
  econstructor.
  apply: re_pure.
  apply: wr_heap_re; eauto.
Qed.

Lemma eval_split Θ1 Θ2 Θ Θ' m n m' A t :
  well_resolved Θ1 m n A t -> wr_heap Θ -> 
  Θ1 ∘ Θ2 => Θ -> eval Θ m Θ' m' ->
  exists Θ1' Θ2' n', 
    well_resolved Θ1' m' n' A t /\ wr_heap Θ' /\
    pad Θ2 Θ2' /\ Θ1' ∘ Θ2' => Θ' /\ n ~>* n'.
Proof with eauto 6 using 
  clc_type, key, lookup, pad, merge, 
  well_resolved, resolve, resolve_wkU, resolve_wkN, 
  all_ptr, All1, All2.
  move=>{Θ1 m n A t}[Θ1 m n A t rm]. move e:(nil)=>Γ tyn.
  move: Γ n A t tyn Θ1 Θ2 Θ Θ' m m' rm e.
  apply: clc_type_ind_nested.
  move=>Γ s l k Θ1 Θ2 Θ Θ' m m' rsm e wr mrg ev; subst.
  { inv rsm; inv ev; try solve_spine.
    exists ((s @ l) :U Θ1).
    exists ((s @ l) :U Θ2).
    exists (s @ l).
    repeat split...
    econstructor.
    move:mrg=>/merge_size[<-_]...
    econstructor... 
    econstructor...
    have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0.
    have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0. }
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ1 Θ2 Θ Θ' 
    m m' rsm e wr mrg ev; subst.
  { inv rsm; inv ev; try solve_spine.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    exists ((Pi A0 B0 s r t) :U Θ1).
    exists ((Pi A0 B0 s r t) :U Θ2).
    exists (Pi A B s r t).
    repeat split...
    econstructor.
    move:mrg=>/merge_size[<-_]...
    econstructor... 
    econstructor... 
    have//=nfA:=nf_typing tyA.
    have//:=resolve_wr_nfi H7 wr1 nfA.
    destruct s; simpl in tyB.
    have//=nfB:=nf_typing tyB.
    have//:=resolve_wr_nfi H8 wr1 nfB.
    have//=nfB:=nf_typing tyB.
    have//:=resolve_wr_nfi H8 wr1 nfB.
    have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0.
    have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0. }
  move=>Γ x A s hs Θ1 Θ2 Θ Θ' m m' rsm e tyA mrg ev.
  { inv rsm; inv ev; try solve_spine.
    have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0.
    have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0. }
  move=>Γ A B m s r t i k tyP ihP tym ihm 
    Θ1 Θ2 Θ Θx n m' rsL e wr mrg ev.
  { inv rsL; inv ev; try solve_spine.
    have[<-_]:=merge_size mrg.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct t.
    { exists ((Lam A0 m0 s U) :U Θ1).
      exists ((Lam A0 m0 s U) :U Θ2).
      exists (Lam A m s U).
      repeat split... 
      econstructor... 
      have[l0[tyA[_ _]]]:=pi_inv tyP.
      have//=nfA:=nf_typing tyA.
      have//:=resolve_wr_nfi H6 (wr_heap_re wr1) nfA.
      destruct s.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm. }
    { exists ((Lam A0 m0 s L) :L Θ1).
      exists (_: Θ2).
      exists (Lam A m s L).
      repeat split... 
      econstructor... 
      have[l0[tyA[_ _]]]:=pi_inv tyP.
      have//=nfA:=nf_typing tyA.
      have//:=resolve_wr_nfi H6 (wr_heap_re wr1) nfA.
      destruct s.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm. }
    { have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0. }
    { have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0. } }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg1 tym ihm tyn ihn
    Θ1 Θ2 Θ Θ' x x' rx e wf mrg2 ev; subst.
  { inv mrg1.
    have[l tyP]:= validity nil_ok tym.
    have[l0[tyA[_[_ tyB]]]]:= pi_inv tyP.
    inv ev; inv rx.
    { have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H5.
      have[Θx1[Θx2[mx[wr[wf'[pd[mrgx rx]]]]]]]:=
        ihm _ _ _ _ _ _ H6 erefl wf mrg4 H.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      inv wr.
      exists Θy. exists Θ2p.
      exists (App mx n).
      repeat split...
      econstructor.
      exact: (merge_sym mrp1).
      eauto.
      apply: resolve_pad...
      apply: red_app... }
    { have[Θx[mrg3 mrg4]]:=merge_splitL mrg2 H5.
      have{ihn}[Θx1[Θx2[nx[wr[wf'[pd[mrgx rx]]]]]]]:=
        ihn _ _ _ _ _ _ H7 erefl wf (merge_sym mrg4) H.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      inv wr.
      exists Θy. exists Θ2p.
      exists (App m nx).
      repeat split...
      econstructor. 
      exact: mrp1.
      apply: resolve_pad... eauto.
      destruct s.
      { apply: clc_conv.
        apply: conv_sub.
        apply: conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: rx.
        apply: clc_app...
        have mrgs:[@nil (elem term)] ∘ nil => nil. simpl...
        have h:=substitution tyB k mrgs tyn... }
      { apply: clc_conv.
        apply: conv_sub.
        apply: conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: rx.
        apply: clc_app...
        have h:=substitutionN tyB tyn... }
      eauto.
      apply: red_app... } 
    { move=>{ihm ihn}.
      have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H5.
      have[G[mrg rs]]:=resolve_lookup H H6 mrg4.
      have[Gx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg) mrg3.
      exists Gx. exists Θ2. inv rs. exists (m'.[n/]).
      have tym':=lam_inv tyP tym.
      repeat split...
      have[wf1 wf2]:=wr_merge_inv mrg2 wf.
      have[wf0 wf3]:=wr_merge_inv H5 wf1.
      have vn:=wr_resolve_value wf3 H7.
      have key:=resolution tyn vn wf3 H7.
      have wr':=lookup_wr H wf.
      have [wr1 wr2]:=wr_merge_inv mrg wr'.
      destruct s.
      { apply: resolve_substU...
        apply: wr_merge...
        apply: merge_sym... }
      { apply: resolve_substL...
        apply: wr_merge...
        apply: merge_sym... }
      apply: substitution...
      apply: lookup_wr...
      apply: star1.
      apply: step_beta. }
    { have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H5.
      have[G[mrg rs]]:=resolve_lookup H0 H6 mrg4.
      have[Gx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg) mrg3.
      have[e1 e2]:=merge_size mrg6.
      have[e3 e4]:=merge_size mrg.
      have[e5 e6]:=merge_size mrg4.
      exists (spine (Ind A0 Cs s0) (rcons ms (Ptr l2)) :U Gx). 
      exists (spine (Ind A0 Cs s0) (rcons ms (Ptr l2)) :U Θ2). 
      exists (App m n).
      repeat split...
      econstructor.
      econstructor.
      rewrite e1. rewrite<-e4. rewrite e6...
      { rewrite<-spine_app_rcons.
        have mrg7: 
          App (spine (Ind A0 Cs s0) ms) (Ptr l2) :U Θ3 ∘
          App (spine (Ind A0 Cs s0) ms) (Ptr l2) :U G =>
          App (spine (Ind A0 Cs s0) ms) (Ptr l2) :U Gx by constructor.
        apply: resolve_app.
        apply: merge_sym mrg7.
        apply: resolve_wkU...
        apply: resolve_wkU... }
      have[nfA[nfCs pms]]:=lookup_wr_ind_inv H0 wf.
      have wr:=lookup_wr H0 wf.
      constructor...
      apply: all_ptr_rcons... }
    { have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H5.
      have[G[mrg rs]]:=resolve_lookup H0 H6 mrg4.
      have[Gx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg) mrg3.
      have[e1 e2]:=merge_size mrg6.
      have[e3 e4]:=merge_size mrg.
      have[e5 e6]:=merge_size mrg4.
      destruct s0.
      { exists (spine (Constr i I U) (rcons ms (Ptr l2)) :U Gx). 
        exists (spine (Constr i I U) (rcons ms (Ptr l2)) :U Θ2). 
        exists (App m n).
        repeat split...
        econstructor.
        econstructor.
        rewrite e1. rewrite<-e4. rewrite e6...
        { rewrite<-spine_app_rcons.
          have mrg7: 
            App (spine (Constr i I U) ms) (Ptr l2) :U Θ3 ∘
            App (spine (Constr i I U) ms) (Ptr l2) :U G =>
            App (spine (Constr i I U) ms) (Ptr l2) :U Gx by constructor.
          apply: resolve_app.
          apply: merge_sym mrg7.
          apply: resolve_wkU...
          apply: resolve_wkU... }
        have[nfI pms]:=lookup_wr_constr_inv H0 wf.
        have wr:=lookup_wr H0 wf.
        constructor...
        apply: all_ptr_rcons... }
      { exists (spine (Constr i I L) (rcons ms (Ptr l2)) :L Gx).
        exists (_: Θ2).
        exists (App m n).
        repeat split...
        econstructor.
        econstructor.
        rewrite e1. rewrite<-e4. rewrite e6...
        { rewrite<-spine_app_rcons.
          have mrg7: _: Θ3 ∘ _: G => _: Gx by constructor.
          apply: resolve_app.
          apply: merge_sym mrg7.
          apply: resolve_wkN...
          apply: resolve_wkN... }
        have[nfI pms]:=lookup_wr_constr_inv H0 wf.
        have wr:=lookup_wr H0 wf.
        constructor...
        apply: all_ptr_rcons... } }
    { have[Θx[mrg3 mrg4]]:=merge_splitL mrg2 H8.
      have e:=lookup_wr_fix H2 wf; subst.
      rewrite<-spine_app_rcons in H4. inv H4.
      have{ihn}[Θx1[Θx2[nx[wr[wf'[pd[mrgx rx]]]]]]]:=
        ihn _ _ _ _ _ _ H10 erefl wf (merge_sym mrg4) H3.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      inv wr.
      exists Θy. exists Θ2p.
      exists (App m nx).
      repeat split...
      rewrite<-spine_app_rcons.
      econstructor.
      apply: mrp1.
      apply: resolve_pad... eauto.
      destruct s.
      { apply: clc_conv.
        apply: conv_sub.
        apply: conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: rx.
        apply: clc_app...
        have mrgs:[@nil (elem term)] ∘ nil => nil. simpl...
        have h:=substitution tyB k mrgs tyn... }
      { apply: clc_conv.
        apply: conv_sub.
        apply: conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: rx.
        apply: clc_app...
        have h:=substitutionN tyB tyn... }
      apply: red_app... }
    { rewrite<-spine_app_rcons in H4.
      inv H4. }
    { move=>{ihn}.
      rewrite<-spine_app_rcons in H. inv H.
      have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H6.
      have[G1[G2[m1[ms1[mrg1[e[rm1 rms1]]]]]]]:=ptr_spine_inv H7; subst.
      have sz:=resolve_spine_size rms1.
      have[G3[mrg5 mrg6]]:=merge_splitR mrg4 mrg1.
      have[G[mrg rs]]:=resolve_lookup H2 rm1 mrg6.
      have[Gx[mrg7 mrg8]]:=merge_splitL (merge_sym mrg) mrg5.
      inv rs.
      have[wf1 wf2]:=wr_merge_inv mrg6 wf.
      have k1:=resolve_fix_inv wf1 rm1.
      have[G4[G5[A1[s1[mrg9[tyF sp]]]]]]:=spine_inv nil_ok tym. inv mrg9.
      have[l4[sb[e[_[tyA' tym']]]]]:=fix_inv tyF; subst.
      have[l5 tyA1]:=validity nil_ok tyF.
      have[e1[e2 e3]]:=merge_re_re mrg5.
      have[e4[e5 e6]]:=merge_re_re mrg6.
      have[e7[e8 e9]]:=merge_re_re mrg7.
      have[G6[mg1 mg2]]:=merge_splitR (merge_sym mrg8) mrg3.
      have[G7[mg3 rsn]]:=resolve_lookup H3 H8 mg2.
      have[i1[I1[s1[ms2 e]]]]:=resolve_constr_spine rsn; subst.
      have e:=merge_pureR mrg7 H9; subst.
      have[G8[mg5 mg6]]:=merge_splitR (merge_sym mg3) mg1.
      have[sz1 sz2]:=merge_size mrg2.
      have[sz3 sz4]:=merge_size mg1.
      have[sz5 sz6]:=merge_size mg3.
      have wf3:=lookup_wr H2 wf.
      have wf4:=lookup_wr H3 wf3.
      have[nfI ap]:=lookup_wr_constr_inv H3 wf3.
      have mrg9: G ∘ G1 => G1.
      { replace G with [G].
        replace G1 with [G1].
        rewrite<-e7.
        rewrite e4.
        rewrite e2.
        apply: merge_re_id.
        rewrite<-pure_re; eauto.
        rewrite<-pure_re; eauto. }
      have rm:=resolve_substU tym' k1 H12 rm1 wf1 mrg9.
      have{}rm: resolve G2 (spine m0.[Ptr l2/] ms) (spine m'.[Fix (size ms) A' m'/] ms1).
      { apply: app_resolve_spine; eauto.
        replace G1 with [G1].
        rewrite e4. rewrite<-e2.
        apply: merge_reL.
        rewrite<-pure_re; eauto. }
      have tyF': nil ⊢ Fix (size ms) A' m' : A' : U.
      { apply: clc_fix; eauto... }
      have tymf:=substitution tym' (key_nil _ _) (merge_nil _) tyF'.
      asimpl in tymf.
      have tymf':=clc_conv sb tymf tyA1.
      have tysp:=app_typing_spine tymf' sp (merge_nil _).
      destruct s0.
      { exists (spine (Constr i I U) ns :U G8).
        exists (spine (Constr i I U) ns :U Θ2).
        exists (spine m'.[Fix (size ms) A' m'/] (rcons ms1 (spine (Constr i1 I1 s1) ms2))).
        repeat split...
        rewrite<-!spine_app_rcons.
        econstructor.
        constructor.
        apply: mg5.
        apply:resolve_wkU; eauto.
        econstructor.
        constructor.
        rewrite<-sz2.
        by rewrite sz3 sz5 sz6.
        apply: resolve_wkU; eauto.
        rewrite<-spine_app_rcons.
        apply: clc_app.
        apply: key_nil.
        constructor.
        all: eauto.
        constructor; eauto.
        constructor.
        apply: merge_sym...
        apply: star1.
        rewrite spine_app_rcons.
        rewrite sz.
        constructor; eauto. }
      { exists (spine (Constr i I L) ns :L G8).
        exists (_: Θ2).
        exists (spine m'.[Fix (size ms) A' m'/] (rcons ms1 (spine (Constr i1 I1 s1) ms2))).
        repeat split...
        rewrite<-!spine_app_rcons.
        econstructor.
        apply: merge_right2.
        apply: mg5.
        apply: resolve_wkN; eauto.
        econstructor.
        constructor.
        rewrite<-sz2.
        by rewrite sz3 sz5 sz6.
        apply: resolve_wkN; eauto.
        rewrite<-spine_app_rcons.
        apply: clc_app.
        apply: key_nil.
        constructor.
        all: eauto.
        constructor; eauto.
        constructor.
        apply: merge_sym...
        apply: star1.
        rewrite spine_app_rcons.
        rewrite sz.
        constructor; eauto. } }
    { rewrite<-spine_app_rcons in H.
      inv H. } }
  move=>Γ A Cs s l1 l2 k ar cCs tyA ihA tyCs ihCs
    Θ1 Θ2 Θ Θ' m m' rsm e wr mrg ev; subst.
  { inv rsm; inv ev; try solve_spine.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    have[<-_]:=merge_size mrg.
    exists (Ind A0 Cs0 s :U Θ1).
    exists (Ind A0 Cs0 s :U Θ2).
    exists (Ind A Cs s).
    repeat split...
    replace (Ind A0 Cs0 s) with (spine (Ind A0 Cs0 s) nil) by eauto.
    constructor...
    have//=nfA:=nf_typing tyA.
    have//:=resolve_wr_nfi H5 wr1 nfA.
    elim: H6 tyCs...
    move=>C1 C2 Cs1 Cs2 rC rCs ih tl. inv tl.
    constructor...
    have//=nfC:=nf_typing H1.
    have//:=resolve_wr_nfi rC wr1 nfC.
    have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0.
    have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0. }
  move=>Γ A s i C Cs//=k ig tyI ihI 
    Θ1 Θ2 Θ Θ' m m' rsm e  wr mrg ev; subst.
  { inv rsm; inv ev; try solve_spine.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    have[<-_]:=merge_size mrg.
    destruct s.
    { exists (Constr i I U :U Θ1).
      exists (Constr i I U :U Θ2).
      exists (Constr i (Ind A Cs U) U).
      repeat split...
      replace (Constr i I U) with (spine (Constr i I U) nil) by eauto.
      constructor...
      have//=nfI:=nf_typing tyI.
      have//:=resolve_wr_nfi H5 wr1 nfI. }
    { exists (Constr i I L :L Θ1).
      exists (_: Θ2).
      exists (Constr i (Ind A Cs L) L).
      repeat split...
      replace (Constr i I L) with (spine (Constr i I L) nil) by eauto.
      constructor...
      have//=nfI:=nf_typing tyI.
      have//:=resolve_wr_nfi H5 wr1 nfI. }
    { have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0. }
    { have[e mrg']:=lookup_subset mrg H5 H; subst. inv H0. } }
  move=>Γ1 Γ2 Γ A Q s s' l k Fs Cs m ms//=leq ar key mrg1 
    tym ihm tyQ ihQ tyFs ihFs Θ1 Θ2 Θ Θ' m0 m' rsm e wr mrg2 ev; subst.
  { inv mrg1.
    inv rsm; inv ev; try solve_spine.
    { have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H2.
      have[Θx1[Θx2[mx[wrs[wf'[pd[mrgx rx]]]]]]]:=
        ihm _ _ _ _ _ _ H5 erefl wr mrg4 H9.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      have[l0 tysp]:=validity nil_ok tym.
      have tyI:=ind_spine (key_nil _ _) tysp.
      inv wrs.
      exists Θy. exists Θ2p.
      exists (Case mx Q Fs).
      repeat split...
      { econstructor.
        apply: merge_sym...
        eauto.
        apply: resolve_pad.
        apply: pad_re...
        eauto.
        elim: H7...
        move=>F1 F2 Fs1 Fs2 rF rFs tl.
        constructor...
        apply: resolve_pad... }
      { have sb: kapp k (spine Q ms) mx <: kapp k (spine Q ms) m.
        { destruct k=>//=.
          apply: conv_sub.
          apply: conv_sym.
          apply: star_conv.
          apply: red_app... }
        have[sp _]:=ind_spine_inv (key_nil _ _) ar tysp.
        have{}sp:=rearity_spine s' sp ar leq (key_nil _ _) tyI.
        have spQ:=app_arity_spine tyQ sp (merge_nil _).
        destruct k=>//=.
        { inv leq.
          have//=tyapp:=clc_app (key_nil _ _) (merge_nil _) spQ tym.
          apply: clc_conv...
          apply: clc_case...
          constructor. }
        { apply: clc_conv... } }
      { apply: red_case... } }
    { have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H2.
      have[G[mrg rs]]:=resolve_lookup H10 H5 mrg4.
      have[Gx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg) mrg3.
      exists Gx. exists Θ2. 
      have[I'[ms'[e[rI sp]]]]:=constr_spine_inv rs; subst.
      have[F'[ig' rF]]:=iget_All2 H7 H9.
      exists (spine F' ms').
      have wr':=lookup_wr H10 wr.
      have[wr1 wr2]:=wr_merge_inv mrg wr'.
      repeat split...
      apply: app_resolve_spine...
      have[G1[G2[A0[s1[mrg7[tyC tysp]]]]]]:=spine_inv nil_ok tym.
      inv mrg7.
      have//=[l1 tyA0]:=validity nil_ok tyC.
      have[A1[C0[Cs0[e1[_[ig0[e2[sb tyI']]]]]]]]:=constr_inv tyC; subst.
      have[l2[l3[_[_[ar1[cCs0[tyA1 tyCs0]]]]]]]:=ind_inv tyI'.
      have[C[ig1[cC tyF']]]:=iget_All2i tyFs ig'.
      have cC0:=iget_All1 ig0 cCs0.
      have{}tysp:=typing_spine_strengthen tysp sb tyA0.
      have//=[cv e]:=typing_spine_constr_ind cC0 tysp erefl; subst.
      have[cvA[cvCs _]]:=ind_inj cv.
      have[Cx[igx cvC]]:=iget_All2 cvCs ig0.
      have e:=iget_iget ig1 igx; subst.
      have tyC0:=iget_All1 ig0 tyCs0.
      have//=tyCI:=substitution tyC0 (key_nil _ _) (merge_nil _) tyI'.
      have h3 : Cx.[Ind A Cs s/] <: C0.[Ind A1 Cs0 s/].
      { apply: conv_sub.
        apply: conv_trans.
        apply: conv_beta.
        apply: conv_sym...
        apply: conv_subst.
        apply: conv_sym... }
      have{}tysp:=typing_spine_strengthen tysp h3 tyCI.
      have//=[l4 tyIsp]:=validity nil_ok tym.
      have[arsp _]:=ind_spine_inv (key_nil _ _) ar tyIsp.
      have tyI:=ind_spine (key_nil _ _) tyIsp.
      have{}arsp:=rearity_spine s' arsp ar leq (key_nil _ _) tyI.
      have spQ:=app_arity_spine tyQ arsp (merge_nil _).
      have[l5[l6[_[_[_[_[tyA tyCs]]]]]]]:=ind_inv tyI.
      have tyCx:=iget_All1 igx tyCs.
      have//={}tyCx:=substitution tyCx (key_nil _ _) (merge_nil _) tyI.
      have h4 :
        kapp k (spine Q ms) (spine (Constr i (Ind A Cs s) s) ms') <:
        kapp k (spine Q ms) (spine (Constr i (Ind A1 Cs0 s) s) ms').
      { apply: conv_sub.
        destruct k=>//=.
        apply: conv_app...
        apply: head_spine_conv.
        apply: conv_constr.
        apply: conv_sym... }
      destruct k=>//=.
      { inv leq.
        have//=tyapp:=clc_app (key_nil _ _) (merge_nil _) spQ tym.
        apply: clc_conv.
        apply: h4. 
        apply: app_typing_spine...
        unfold mkcase.
        apply: typing_spine_constrU...
        asimpl; eauto.
        move=>x; asimpl=>h. inv h.
        eauto. }
      { apply: clc_conv.
        apply: h4.
        apply: app_typing_spine...
        unfold mkcase.
        apply: typing_spine_constrL...
        asimpl; eauto.
        move=>x; asimpl=>h. inv h.
        eauto. }
      apply: star1.
      constructor... }
    { have[e mrg']:=lookup_subset mrg2 H5 H; subst. inv H0. }
    { have[e mrg']:=lookup_subset mrg2 H5 H; subst. inv H0. } }
  move=>Γ k A m l _ tyA ihA tym ihm Θ1 Θ2 Θ Θ' m0 m' rsm e wr mrg ev.
  { inv rsm; inv ev; try solve[solve_spine].
    have[<-_]:=merge_size mrg.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    have tyF:nil ⊢ Fix k A m : A : U.
      econstructor...
    have//=nfA:=nf_typing tyA.
    have//=nfm:=nf_typing tym.
    have nfA0:=resolve_wr_nfi H5 wr1 nfA.
    have nfm1:=resolve_wr_nfi H6 wr1 nfm.
    exists (Fix k A0 m1 :U Θ1).
    exists (Fix k A0 m1 :U Θ2).
    exists (Fix k A m).
    repeat split...
    constructor...
    rewrite<-spine_app_rcons in H1. inv H1.
    rewrite<-spine_app_rcons in H1. inv H1. }
  move=>Γ A B m s i sb tym ihm tyB ihB
    Θ1 Θ2 Θ Θ' m1 m2 rsm e wr mrg ev; subst.
  { have[G1[G2[n'[wrs[wr1[pd1[mrg' st]]]]]]]:=
      ihm _ _ _ _ _ _ rsm erefl wr mrg ev.
    inv wrs.
    exists G1. exists G2. exists n'.
    repeat split... }
Qed.

Theorem evaluation Θ Θ' m m' n A t :
  wr_heap Θ -> well_resolved Θ m m' A t -> eval Θ m Θ' n -> 
  exists n', well_resolved Θ' n n' A t /\ wr_heap Θ' /\ m' ~>* n'.
Proof.
  move=>wr wrs ev.
  have mrg:=merge_reR Θ.
  have[G1[G2[n'[wrs'[wr'[pd[mrg' rd]]]]]]]:=eval_split wrs wr mrg ev.
  have k:=pad_pure pd.
  have e:=merge_pureR mrg' k; subst.
  exists n'; eauto.
Qed.

Theorem type_resolved m A t : 
  nil ⊢ m : A : t -> well_resolved nil m m A t.
Proof.
  move=>ty.
  constructor.
  have//:=resolve_type_refl nil ty.
  exact: ty.
Qed.
