From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive agree_ren : (var -> var) ->
  context term -> context term -> Prop :=
| agree_ren_nil ξ :
  agree_ren ξ nil nil
| agree_ren_ty Γ Γ' ξ m s :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (m :{s} Γ) (m.[ren ξ] :{s} Γ')
| agree_ren_n Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (_: Γ) (_: Γ')
| agree_ren_wkU Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (ξ >>> (+1)) (Γ) (m :U Γ')
| agree_ren_wkN Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren (ξ >>> (+1)) (Γ) (_: Γ').

Lemma agree_ren_refl Γ : agree_ren id Γ Γ.
Proof with eauto using agree_ren.
  elim: Γ...
  move=>[[A s]|] Γ ih.
  have:(agree_ren (upren id) (A :{s} Γ) (A.[ren id] :{s} Γ))...
  by asimpl.
  have:(agree_ren (upren id) (_: Γ) (_: Γ))...
  by asimpl.
Qed.

Lemma agree_ren_key Γ Γ' ξ s : 
  agree_ren ξ Γ Γ' -> Γ |> s -> Γ' |> s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Γ Γ' ξ}...
  move=>Γ Γ' ξ m s agr ih t k.
  inv k...
  move=>Γ Γ' ξ agr ih t k.
  inv k...
  move=>Γ Γ' ξ m agr ih [] /ih k...
Qed.

Lemma agree_ren_re_re Γ Γ' ξ :
  agree_ren ξ Γ Γ' -> agree_ren ξ [Γ] [Γ'].
Proof with eauto using agree_ren.
  elim=>{Γ Γ' ξ}... move=>Γ Γ' ξ m[]...
Qed.

Lemma agree_ren_has Γ Γ' ξ x s A :
  agree_ren ξ Γ Γ' ->
  has Γ x s A -> has Γ' (ξ x) s A.[ren ξ].
Proof with eauto using agree_ren_key.
  move=>agr. elim: agr x s A=>{Γ Γ' ξ}.
  move=>ξ x s A hs. inv hs.
  move=>Γ Γ' ξ m s agr ih x t A hs. 
    inv hs; asimpl.
    replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)]
      by autosubst.
    constructor...
    replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)]
      by autosubst.
    constructor...
  move=>Γ Γ' ξ agr ih x s A hs.
    inv hs; asimpl.
    replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)]
      by autosubst.
    constructor...
  move=>Γ Γ' ξ m agr ih x s A /ih hs.
    asimpl.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)]
      by autosubst.
    constructor...
  move=>Γ Γ' ξ agr ih x s A /ih hs.
    asimpl.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)]
      by autosubst.
    constructor...
Qed.

Lemma merge_agree_ren_inv Γ Γ' Γ1 Γ2 ξ :
  agree_ren ξ Γ Γ' -> merge Γ1 Γ2 Γ ->
  exists Γ1' Γ2',
    merge Γ1' Γ2' Γ' /\
    agree_ren ξ Γ1 Γ1' /\
    agree_ren ξ Γ2 Γ2'.
Proof with eauto 6 using merge, agree_ren.
  move=>agr. elim: agr Γ1 Γ2=>{Γ Γ' ξ}.
  move=>ξ Γ1 Γ2 mrg. inv mrg.
    exists nil. exists nil...
  move=>Γ Γ' ξ m s agr ih Γ1 Γ2 mrg. inv mrg.
    move:H2=>/ih[G1[G2[mrg[agr1 agr2]]]]{ih}.
      exists (m.[ren ξ] :U G1).
      exists (m.[ren ξ] :U G2)...
    move:H2=>/ih[G1[G2[mrg[agr1 agr2]]]]{ih}.
      exists (m.[ren ξ] :L G1).
      exists (_: G2)...
    move:H2=>/ih[G1[G2[mrg[agr1 agr2]]]]{ih}.
      exists (_: G1).
      exists (m.[ren ξ] :L G2)...
  move=>Γ Γ' ξ agr ih Γ1 Γ2 mrg. inv mrg.
    move:H2=>/ih[G1[G2[mrg[agr1 agr2]]]]{ih}.
    exists (_: G1).
    exists (_: G2)...
  move=>Γ Γ' ξ m agr ih Γ1 Γ2 /ih[G1[G2[mrg[agr1 agr2]]]].
    exists (m :U G1).
    exists (m :U G2)...
  move=>Γ Γ' ξ agr ih Γ1 Γ2 /ih[G1[G2[mrg[agr1 agr2]]]].
    exists (_: G1).
    exists (_: G2)...
Qed.

Lemma arity_ren s l A ξ : arity s l A -> arity s l A.[ren ξ].
Proof with eauto using arity.
  move=>ar. elim: ar ξ=>//={A}...
  move=>A B ar ih ξ.
  constructor.
  asimpl.
  apply: ih.
Qed.

Definition n_ren (ξ : var -> var) x :=
  ξ x = x /\ forall i, (~x = i -> ~ξ i = x) /\ (~i = 0 -> ~ξ i = 0).

Lemma n_ren0 ξ : n_ren (upren ξ) 0.
Proof.
  split; eauto.
  move=> i. elim: i ξ=>//=.
Qed.

Lemma n_ren_up ξ x :
  n_ren ξ x -> n_ren (upren ξ) x.+1.
Proof.
  move=>[e h]. split.
  asimpl; eauto.
  elim; asimpl; eauto.
  move=>n [ih1 ih2]. split; eauto.
  move=>neq.
  have pf : ~x = n by eauto.
  have[h1 h2]:=h n.
  move: pf=>/h1; eauto.
Qed.

Lemma noccurs_ren x m ξ :
  noccurs x m -> n_ren ξ x -> noccurs x m.[ren ξ].
Proof with eauto using noccurs, n_ren_up, and.
  move=>no. move: x m no ξ.
  apply: noccurs_ind_nested...
  move=>x y neq ξ [e h].
  { have{h}[h _]:=h y.
    move:neq=>/h neq.
    constructor. eauto. }
  move=>x A B s r t nA ihA nB ihB ξ n. asimpl.
  { constructor. apply: ihA... apply: ihB... }
  move=>x A m s t nA ihA nm ihm ξ n. asimpl.
  { constructor. apply: ihA... apply: ihm... }
  move=>x A Cs s nA ihA nCs ihCs ξ n. asimpl.
  { constructor. apply: ihA...
    elim: ihCs=>//=. constructor.
    move=>m ls ihm _ ih.
    constructor. asimpl...
    asimpl in ih... }
  move=>x m Q Fs nm ihm nQ ihQ nFs ihFs ξ. asimpl.
  { constructor. apply: ihm... apply: ihQ...
    elim: ihFs=>//=. constructor.
    move=>m0 ls ihm0 _ ih.
    constructor. asimpl...
    asimpl in ih... }
  move=>x k A m nA ihA nm ihm ξ n. asimpl.
  { constructor. apply: ihA... apply: ihm... }
Qed.

Lemma noccurs_ren_All1 x ms ξ :
  All1 (noccurs x) ms -> n_ren ξ x ->
  All1 (noccurs x) ms..[ren ξ].
Proof.
  move=>no. elim: no ξ=>//={ms}.
  move=>ξ n. constructor.
  move=> m ms nM nMs ih ξ n.
  constructor.
  apply: noccurs_ren; eauto.
  apply: ih; eauto.
Qed.

Lemma pos_ren x A ξ :
  pos x A -> n_ren ξ x -> pos x A.[ren ξ].
Proof.
  move=> p. elim: p ξ=>{x A}//=.
  move=>x ms nms ξ [e h].
  rewrite spine_subst=>//=.
  rewrite e. constructor. by apply: noccurs_ren_All1.
  move=>x A B s r t nA pB ihB ξ n.
  constructor.
  by apply: noccurs_ren.
  asimpl. apply: ihB. by apply: n_ren_up.
Qed.

Lemma constr_ren i s C ξ :
  constr i s C -> n_ren ξ i -> constr i s C.[ren ξ].
Proof.
  move=>c. elim: c ξ=>{i s C}.
  move=>x s ms no ξ [e h].
  { rewrite spine_subst. asimpl.
    rewrite e.
    constructor.
    elim: no=>//=. constructor.
    move=>m ls nm nms ih.
    constructor.
    apply: noccurs_ren; eauto; constructor; eauto.
    apply: ih. }
  move=>s t x A B leq pA nB cB ihB ξ n=>//=.
  { apply: constr_pos; eauto.
    apply: pos_ren; eauto.
    asimpl. apply: noccurs_ren; eauto. apply: n_ren0.
    asimpl. apply: ihB. apply: n_ren_up; eauto. }
  move=>s t x A B leq nA cB ihB ξ n=>//=.
  { apply: constr_pi; eauto.
    apply: noccurs_ren; eauto.
    asimpl. apply: ihB. apply: n_ren_up; eauto. }
Qed.

Lemma respine_respine0 k s s' c I :
  (forall Q, respine k s Q c I = (s', kapp k Q c)) ->
  (forall Q, respine0 Q I = Q).
Proof.
  elim: I=>//=.
  move=>m _ n _ h Q.
  destruct k.
  have{}[e1 e2]//:=h Q.
  have{}[e1 e2]//:=h Q.
Qed.

Lemma respine_ren1 k s s' (I : var -> term) :
  (forall i c Q, respine k s Q c (I i) = (s', kapp k Q c)) ->
  (forall i c Q, respine k s Q c (I i).[ren (+1)] = (s', kapp k Q c)).
Proof.
  move=>h i. move e:(I i)=>n.
  elim: n e h=>//=.
  move=>x e h c Q.
  { erewrite<-(h i)=>//.
    by rewrite e. }
  move=>s0 l e h c Q.
  { erewrite<-(h i)=>//.
    by rewrite e. }
  move=>A _ B _ s0 r t e h c Q.
  { have:=h i c (Var 0).
    rewrite e=>//=.
    destruct k=>//=.
    destruct (respine U s (ids 1) (App c.[ren (+1)] (Var 0)) B)=>//.
    destruct (respine L s (ids 1) (App c.[ren (+1)] (Var 0)) B)=>//. }
  move=>A _ m _ s0 t e h c Q.
  { have:=h i c (Var 0).
    rewrite e=>//=.
    destruct k=>//=.
    move=>[]->//.
    move=>[]->//. }
  move=>m _ n _ e h c Q.
  { have:=h i c (Var 0).
    rewrite e=>//=.
    destruct k=>//=. }
  move=>A _ Cs s0 e h c Q.
  { have:=h i c (Var 0).
    rewrite e=>//=.
    destruct k=>//=.
    move=>[]->//.
    move=>[]->//. }
  move=>i0 m _ t e h c Q.
  { have:=h i c (Var 0).
    rewrite e=>//=.
    destruct k=>//=.
    move=>[]->//.
    move=>[]->//. }
  move=>m _ Q _ Fs e h c Q0.
  { have:=h i c (Var 0).
    rewrite e=>//=.
    destruct k=>//=.
    move=>[]->//.
    move=>[]->//. }
  move=>k0 A _ m _ e h c Q.
  { have:=h i c (Var 0).
    rewrite e=>//=.
    destruct k=>//=.
    move=>[]->//.
    move=>[]->//. }
  move=>l e h c Q.
  { have:=h i c Q.
    rewrite e=>//=. }
Qed.

Lemma respine_up k s I :
  (forall i Q c, respine k s Q c (I i) = (s, kapp k Q c)) ->
  (forall i Q c, respine k s Q c (up I i) = (s, kapp k Q c)).
Proof.
  move=>h i. elim: i I h=>//=.
  move=>I h Q c. destruct k=>//=.
  move=>n ih I h Q c. asimpl.
  by apply: respine_ren1.
Qed.

Lemma rearity_ren k s s' l I A ξ :
  arity s l A -> (rearity k s' I A).[ren ξ] = rearity k s' I.[ren ξ] A.[ren ξ].
Proof.
  move=>ar. elim: ar I ξ s'=>{A}//=.
  move=>I ξ s'. destruct k=>//.
  move=>A B ar ih I ξ s'. asimpl.
  rewrite ih. by asimpl.
Qed.

Lemma respine0_I_ren Q I ξ :
  (forall Q, respine0 Q I = Q) -> Q.[ren ξ] = respine0 Q.[ren ξ] I.[ren ξ].
Proof.
  elim: I ξ Q=>//=.
  move=>m _ n _ ξ Q h.
  have//=:=h (Var 0).
Qed.

Lemma respine_I_ren k s s' Q c I ξ :
  (forall Q c, respine k s Q c I = (s', kapp k Q c)) ->
  s' = (respine k s Q.[ren ξ] c.[ren ξ] I.[ren ξ]).1 /\
  kapp k Q.[ren ξ] c.[ren ξ] = (respine k s Q.[ren ξ] c.[ren ξ] I.[ren ξ]).2.
Proof.
  elim: I ξ Q c=>//=.
  move=>x ξ Q c h.
  { destruct k=>//=.
    have[->]//:=h Q c.
    have[->]//:=h Q c. }
  move=>t i ξ c Q h.
  { destruct k=>//=.
    have[->]//:=h Q c.
    have[->]//:=h Q c. }
  move=>A _ B _ s0 r t ξ c Q h.
  { have{h}:=h (Var 0) c.
    destruct k=>//=.
    destruct (respine U s (ids 1) (App c.[ren (+1)] (Var 0)) B)=>//.
    destruct (respine L s (ids 1) (App c.[ren (+1)] (Var 0)) B)=>//. }
  move=>A _ m _ r t ξ Q c h.
  { destruct k=>//=.
    have[->]//:=h Q c.
    have[->]//:=h Q c. }
  move=>m _ n _ ξ c Q h.
  { have{h}:=h (Var 0) c.
    destruct k=>//=. }
  move=>A _ Cs r ξ Q c h.
  { destruct k=>//=.
    have[->]//:=h Q c.
    have[->]//:=h Q c. }
  move=>i m _ t ξ Q c h.
  { destruct k=>//=.
    have[->]//:=h Q c.
    have[->]//:=h Q c. }
  move=>m _ Q _ Fs ξ Q0 c h.
  { destruct k=>//=.
    have[->]//:=h Q c.
    have[->]//:=h Q c. }
  move=>k0 A _ m _ ξ Q c h.
  { destruct k=>//=.
    have[->]//:=h Q c.
    have[->]//:=h Q c. }
  move=>l ξ Q c h.
  { destruct k=>//=.
    have[->]//:=h Q c.
    have[->]//:=h Q c. }
Qed.

Lemma kapp_ren k m n ξ : (kapp k m n).[ren ξ] = kapp k m.[ren ξ] n.[ren ξ].
Proof. destruct k=>//=. Qed.

Lemma respine0_spine'_I_ren Q I ms ξ :
  (forall Q, respine0 Q I = Q) ->
  (respine0 Q (spine' I ms)).[ren ξ] = respine0 Q.[ren ξ] (spine' I ms).[ren ξ].
Proof.
  elim: ms Q ξ=>//=.
  move=>Q ξ h. rewrite h. by apply: respine0_I_ren.
  move=>a l ih Q ξ h.
  rewrite ih=>//.
Qed.

Lemma respine_spine'_I_ren k s s' Q c I ms ξ :
  (forall Q c, respine k s Q c I = (s', kapp k Q c)) ->
  (respine k s Q c (spine' I ms)).1 =
    (respine k s Q.[ren ξ] c.[ren ξ] (spine' I ms).[ren ξ]).1 /\
  (respine k s Q c (spine' I ms)).2.[ren ξ] =
    (respine k s Q.[ren ξ] c.[ren ξ] (spine' I ms).[ren ξ]).2.
Proof.
  elim: ms Q c ξ=>//=.
  move=>Q c ξ h.
  rewrite h=>//=.
  rewrite kapp_ren.
  by apply: respine_I_ren.
  move=>a l ih Q c ξ h.
  destruct k=>//=.
  rewrite respine0_spine'_I_ren; eauto.
  by apply: respine_respine0.
  rewrite respine0_spine'_I_ren; eauto.
  by apply: respine_respine0.
  Unshelve. all: eauto.
Qed.

Lemma respine_spine_I_ren k s s' I :
  (forall Q c, respine k s Q c I = (s', kapp k Q c)) ->
  forall Q c ms ξ,
    (respine k s Q c (spine I ms)).1 =
      (respine k s Q.[ren ξ] c.[ren ξ] (spine I ms).[ren ξ]).1 /\
    (respine k s Q c (spine I ms)).2.[ren ξ] =
      (respine k s Q.[ren ξ] c.[ren ξ] (spine I ms).[ren ξ]).2.
Proof.
  move=>h Q c ms ξ.
  rewrite spine_spine'_rev.
  by apply: respine_spine'_I_ren.
Qed.

Lemma constr_respine_ren x s' C :
  constr x s' C ->
  forall k s I, (forall i Q c, respine k s Q c (I i) = (s, kapp k Q c)) ->
  forall Q c ξ,
    (respine k s Q c C.[I]).1 =
      (respine k s Q.[ren ξ] c.[ren ξ] C.[I].[ren ξ]).1 /\
    (respine k s Q c C.[I]).2.[ren ξ] =
      (respine k s Q.[ren ξ] c.[ren ξ] C.[I].[ren ξ]).2.
Proof.
  move=>cn. elim: cn=>{x s' C}.
  move=>x s' ms nms k s0 I h Q c ξ.
  { rewrite!spine_subst. asimpl.
    pose proof (respine_spine_I_ren (h x) Q c ms..[I] ξ) as X.
    rewrite!spine_subst in X.
    by asimpl in X. }
  move=>s t x A B leq pA nB cB ih k s0 I h Q c ξ.
  { asimpl.
    have/ih{}ih:=respine_up h.
    pose proof (ih Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) (upren ξ)) as hx.
    asimpl in hx.
    replace (Var 0) with (ids 0) in hx by autosubst.
    replace (Var 0) with (ids 0) by autosubst.
    remember (respine k s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as p1.
    remember (respine k s0 Q.[ren (ξ >>> (+1))] (App c.[ren (ξ >>> (+1))] (ids 0))
       B.[ids 0 .: I >> ren (ξ >>> (+1))]) as p2.
    destruct p1. destruct p2.
    split; eauto.
    asimpl. simpl in hx. destruct hx.
    repeat f_equal; eauto. }
  move=>s t x A B leq nA cB ih k s0 I h Q c ξ.
  { asimpl.
    have/ih{}ih:=respine_up h.
    pose proof (ih Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) (upren ξ)) as hx.
    asimpl in hx.
    replace (Var 0) with (ids 0) in hx by autosubst.
    replace (Var 0) with (ids 0) by autosubst.
    remember (respine k s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as p1.
    remember (respine k s0 Q.[ren (ξ >>> (+1))] (App c.[ren (ξ >>> (+1))] (ids 0))
       B.[ids 0 .: I >> ren (ξ >>> (+1))]) as p2.
    destruct p1. destruct p2.
    split; eauto.
    asimpl. simpl in hx. destruct hx.
    repeat f_equal; eauto. }
Qed.

Lemma All2_case_ren Γ Γ' n k s s' A Q Fs Cs Cs' ξ :
  All2i (fun i F C =>
    constr 0 s C /\
    let I := Ind A Cs' s in
    let T := mkcase k s' I Q (Constr i I s) C in
    forall Γ' ξ, agree_ren ξ Γ Γ' ->
      Γ' ⊢ F.[ren ξ] : T.2.[ren ξ] : T.1) n Fs Cs ->
  agree_ren ξ Γ Γ' ->
  All2i (fun i F C =>
    constr 0 s C /\
    let I := Ind A.[ren ξ] Cs'..[up (ren ξ)] s in
    let T := mkcase k s' I Q.[ren ξ] (Constr i I s) C in
    Γ' ⊢ F : T.2 : T.1) n Fs..[ren ξ] Cs..[up (ren ξ)].
Proof.
  elim: Fs Γ Γ' n s A Q Cs ξ=>//=.
  move=>Γ Γ' n s A Q Cs ξ h agr. inv h.
  { constructor. }
  move=>F Fs ih Γ Γ' n s A Q Cs ξ h agr.
  inv h. inv H2.
  constructor.
  { split.
    asimpl.
    apply: constr_ren; eauto. apply: n_ren0.
    have{H0}tyF:=H0 _ _ agr.
    unfold mkcase in tyF.
    have h: ∀ i Q c, respine k s' Q c ((Ind A Cs' s .: ids) i) = (s', kapp k Q c).
    { move=>[|i] Q0 c; asimpl.
      destruct k=>//.
      destruct k=>//. }
    have {h}[e1 e2]:=constr_respine_ren H h Q (Constr n (Ind A Cs' s) s) ξ.
    rewrite e1 in tyF=>{e1}.
    rewrite e2 in tyF=>{e2}.
    asimpl in tyF.
    unfold mkcase.
    asimpl. eauto. }
  { apply: ih; eauto. }
Qed.

Lemma rename_ok Γ Γ' m A s ξ :
  Γ ⊢ m : A : s -> agree_ren ξ Γ Γ' -> Γ' ⊢ m.[ren ξ] : A.[ren ξ] : s.
Proof with eauto using 
  clc_type, agree_ren, agree_ren_key, agree_ren_re_re.
  move=>ty. move: Γ m A s ty Γ' ξ.
  apply: clc_type_ind_nested=>//=.
  move=>Γ s l k Γ' ξ agr. asimpl...
  move=>Γ A B [] r t i k tyA ihA tyB ihB Γ' ξ agr.
  { asimpl.
    apply: clc_pi... }
  { asimpl.
    apply: clc_pi... }
  move=>Γ x A s hs Γ' ξ agr.
  { asimpl. 
    apply: clc_var.
    apply: agree_ren_has... }
  move=>Γ A B m s r t i k tyP ihP tym ihm Γ' ξ agr.
  { asimpl.
    apply: clc_lam...
    move:(ihP _ _ (agree_ren_re_re agr)). 
    asimpl... }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn Γ' ξ agr.
  { asimpl.
    move:(merge_agree_ren_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(ihm _ _ agr1)=>{ihm}tym.
    move:(ihn _ _ agr2)=>{ihn}tyn.
    move:(agree_ren_key agr2 k)=>{}k.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    apply: clc_app...
    asimpl in tym... }
  move=>Γ A Cs s l1 l2 k ar ctr tyA ihA tyCs ihCs Γ' ξ agr.
  { asimpl.
    apply: clc_indd...
    apply: arity_ren...
    move=>{agr}.
    elim: ctr ξ=>//=...
    { move=>_. constructor. }
    { move=>m ls c h ih ξ. asimpl.
      constructor.
      apply: constr_ren... apply: n_ren0.
      have:=ih ξ... }
    elim: ihCs=>//=.
    { constructor. }
    { move=>m ls ihm hls ihls. asimpl.
      constructor... } }
  move=>Γ A s i C Cs k ig ty ih Γ' ξ agr.
  { replace (C.[Ind A Cs s/].[ren ξ])
      with (C.[up (ren ξ)]).[Ind A.[ren ξ] Cs..[up (ren ξ)] s/]
        by autosubst.
    apply: clc_constr...
    apply: iget_subst... }
  move=>Γ1 Γ2 Γ A Q s s' l k Fs Cs m ms leq ar key mrg tym ihm tyQ ihQ tyFs ihFs Γ' ξ agr.
  { rewrite kapp_ren.
    rewrite spine_subst.
    have[G1[G2[mrg'[agr1 agr2]]]]:=merge_agree_ren_inv agr mrg.
    have ar':=arity_ren ξ ar.
    have{}ihm:=ihm _ _ agr1. rewrite spine_subst in ihm.
    have{}ihQ:=ihQ _ _ (agree_ren_re_re agr2).
    rewrite (rearity_ren k s' (Ind A Cs s) ξ ar) in ihQ.
    apply: clc_case.
    apply: leq.
    eauto.
    apply: agree_ren_key.
    apply: agr1.
    all: eauto.
    apply: All2_case_ren; eauto. }
  move=>Γ k0 A m l k tyA ihA tym ihm Γ' ξ agr.
  { asimpl.
    apply: clc_fix.
    apply: agree_ren_key; eauto.
    apply: ihA; eauto.
    replace A.[ren ξ].[ren (+1)] with A.[ren (+1)].[ren (upren ξ)]
      by autosubst.
    apply: ihm.
    by constructor. }
  move=>Γ A B m s i sb tym ihm tyB ihB Γ' ξ agr.
  { move:(ihm _ _ agr)=>{ihm}tym.
    move:(ihB _ _ (agree_ren_re_re agr))=>{ihB}tyB.
    apply: clc_conv.
    apply: sub_subst...
    by apply: tym.
    by apply: tyB. }
Qed.

Lemma has_ok Γ x A s :
  ok Γ -> has Γ x s A -> exists l, [Γ] ⊢ A : s @ l : U.
Proof with eauto using agree_ren, agree_ren_refl.
  move=> wf. elim: wf s x A=>{Γ}.
  move=>s x A hs. inv hs.
  move=>Γ A s l wf ih tyA t x B hs. inv hs.
  { exists l.
    replace (t @ l) with (t @ l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    destruct t; simpl... }
  { move:H5=>/ih{ih}[i ty].
    exists i.
    replace (t @ i) with (t @ i).[ren (+1)] by autosubst.
    apply: rename_ok; eauto... }
  move=>Γ wf ih s x A hs. inv hs.
  { move:H0=>/ih{ih}[i ty].
    exists i.
    replace (s @ i) with (s @ i).[ren (+1)] by autosubst.
    apply: rename_ok; eauto... }
Qed.

Lemma weakeningU Γ m A B s :
  Γ ⊢ m : A : s -> B :U Γ ⊢ m.[ren (+1)] : A.[ren (+1)] : s.
Proof with eauto using agree_ren, agree_ren_refl.
  move=>ty. apply: rename_ok...
Qed.

Lemma weakeningN Γ m A s :
  Γ ⊢ m : A : s -> _: Γ ⊢ m.[ren (+1)] : A.[ren (+1)] : s.
Proof with eauto using agree_ren, agree_ren_refl.
  move=>ty. apply: rename_ok...
Qed.

Lemma eweakeningU Γ m m' A A' B s :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A : s -> B :U Γ ⊢ m' : A' : s.
Proof.  
  move=>*; subst. by apply: weakeningU.
Qed.

Lemma eweakeningN Γ m m' A A' s :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A : s -> _: Γ ⊢ m' : A' : s.
Proof.  
  move=>*; subst. by apply weakeningN.
Qed.
