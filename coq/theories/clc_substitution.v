From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Δ ⊢ σ ⊣ Γ" (at level 50, σ, Γ at next level).

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil σ :
  nil ⊢ σ ⊣ nil
| agree_subst_ty Δ σ Γ s A :
  Δ ⊢ σ ⊣ Γ ->
  A.[σ] :{s} Δ ⊢ up σ ⊣ A :{s} Γ
| agree_subst_n Δ σ Γ :
  Δ ⊢ σ ⊣ Γ ->
  _: Δ ⊢ up σ ⊣ _: Γ
| agree_subst_wkU Δ σ Γ n A :
  Δ ⊢ σ ⊣ Γ ->
  [Δ] ⊢ n : A.[σ] : U ->
  Δ ⊢ n .: σ ⊣ A :U Γ
| agree_subst_wkL Δ1 Δ2 Δ σ Γ n A :
  Δ1 ∘ Δ2 => Δ ->
  Δ1 ⊢ σ ⊣ Γ ->
  Δ2 ⊢ n : A.[σ] : L ->
  Δ ⊢ n .: σ ⊣ A :L Γ
| agree_subst_wkN Δ σ Γ n :
  Δ ⊢ σ ⊣ Γ ->
  Δ ⊢ n .: σ ⊣ _: Γ
| agree_subst_conv Δ σ Γ A B s l :
  A <: B ->
  [Δ] ⊢ B.[ren (+1)].[σ] : s @ l : U ->
  [Γ] ⊢ B : s @ l : U ->
  Δ ⊢ σ ⊣ A :{s} Γ ->
  Δ ⊢ σ ⊣ B :{s} Γ
where "Δ ⊢ σ ⊣ Γ" := (agree_subst Δ σ Γ).

Lemma agree_subst_key Δ σ Γ s :
  Δ ⊢ σ ⊣ Γ -> Γ |> s -> Δ |> s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Δ σ Γ}...
  move=>Δ σ Γ s A agr ih t k. inv k...
  move=>Δ σ Γ agr ih t k. inv k...
  move=>Δ σ Γ n A agr ih tyn t k. inv k...
  move=>Δ1 Δ2 Δ σ Γ n A mrg agr ih tyn t k. inv k.
    move:(ih _ H3)=>{H3}ih.
    apply: merge_impureL...
  move=>Δ1 Δ2 Δ σ agr ih t k. inv k...
  move=>Δ σ Γ A B s l sb tyB1 tyB2 agr ih t k. inv k...
Qed.

Lemma agree_subst_refl Γ : Γ ⊢ ids ⊣ Γ.
Proof with eauto using agree_subst.
  elim: Γ...
  move=>[[A s]|] Γ agr.
  have: A.[ids] :{s} Γ ⊢ up ids ⊣ A :{s} Γ... by asimpl.
  have: _: Γ ⊢ up ids ⊣ _: Γ... by asimpl.
Qed.
#[global] Hint Resolve agree_subst_refl.

Lemma agree_subst_has Δ σ Γ x s A :
  Δ ⊢ σ ⊣ Γ -> has Γ x s A -> Δ ⊢ σ x : A.[σ] : s.
Proof with eauto using agree_subst, agree_subst_key.
  move=> agr. elim: agr x s A=>{Δ σ Γ}.
  move=>σ x s A hs. inv hs.
  move=>Δ σ Γ s A agr ih x t B hs. inv hs.
  { asimpl.
    replace A.[σ >> ren (+1)] with A.[σ].[ren (+1)] 
      by autosubst.
    apply: clc_var.
    constructor... }
  { asimpl.
    replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)] 
      by autosubst.
    apply: eweakeningU... }
  move=>Δ σ Γ agr ih x s A hs. inv hs.
  { asimpl. 
    replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)] 
      by autosubst.
    apply: eweakeningN... }
  move=>Δ σ Γ n A agr ih tyn x s B hs. inv hs.
  { asimpl.
    rewrite<-pure_re in tyn... }
  { asimpl... }
  move=>Δ1 Δ2 Δ σ Γ n A mrg agr ih tyn x s B hs. inv hs.
  { asimpl.
    move:(agree_subst_key agr H5)=>{H5}k.
    have->:=(merge_pureL mrg k)... }
  move=>Δ σ Γ n agr ih x s A hs. inv hs.
  { asimpl... }
  move=>Δ σ Γ A B s l sb tyB1 tyB2 agr ih x t C hs. inv hs.
  { apply: clc_conv. 
    apply: sub_subst.
    apply: sub_ren...
    apply: ih.
    constructor...
    eauto. }
  { apply: ih.
    constructor... }
Qed.

Lemma agree_subst_re Δ σ Γ : Δ ⊢ σ ⊣ Γ -> [Δ] ⊢ σ ⊣ [Γ].
Proof with eauto using agree_subst, agree_subst_key.
  elim=>{Δ σ Γ}...
  move=>Δ σ Γ [] A agr1 agr2//=...
  move=>Δ σ Γ n A agr1 agr2 ty//=.
    apply: agree_subst_wkU...
    by rewrite<-re_invo.
  move=>Δ1 Δ2 Δ σ Γ n A mrg agr1 agr2 tyn//=.
    apply: agree_subst_wkN...
    move: (merge_re_re mrg)=>[_[<-_]]...
  move=>Δ σ Γ A B [] l sb tyB1 tyB2 agr1 agr2//=.
    apply: agree_subst_conv...
    rewrite<-re_invo...
    rewrite<-re_invo...
Qed.

Lemma merge_agree_subst_inv Δ σ Γ1 Γ2 Γ :
  Δ ⊢ σ ⊣ Γ -> Γ1 ∘ Γ2 => Γ ->
  exists Δ1 Δ2,
    Δ1 ∘ Δ2 => Δ /\ Δ1 ⊢ σ ⊣ Γ1 /\ Δ2 ⊢ σ ⊣ Γ2.
Proof with eauto 6 using merge, agree_subst, agree_subst_key.
  move=>agr. elim: agr Γ1 Γ2=>{Δ σ Γ}.
  move=>σ Γ1 Γ2 mrg. inv mrg. exists nil. exists nil...
  move=>Δ σ Γ s A agr ih Γ1 Γ2 mrg. inv mrg.
  { move:(ih _ _ H2)=>{H2 ih}[G1[G2[mrg[agr1 agr2]]]].
    exists (A.[σ] :U G1).
    exists (A.[σ] :U G2)... }
  { move:(ih _ _ H2)=>{H2 ih}[G1[G2[mrg[agr1 agr2]]]].
    exists (A.[σ] :L G1).
    exists (_: G2)... }
  { move:(ih _ _ H2)=>{H2 ih}[G1[G2[mrg[agr1 agr2]]]].
    exists (_: G1).
    exists (A.[σ] :L G2)... }
  move=>Δ σ Γ agr ih Γ1 Γ2 mrg. inv mrg.
  { move:(ih _ _ H2)=>{H2 ih}[G1[G2[mrg[agr1 agr2]]]].
    exists (_: G1).
    exists (_: G2)... }
  move=>Δ σ Γ n A agr ih tyn Γ1 Γ2 mrg. inv mrg.
  { move:(ih _ _ H2)=>{H2 ih}[G1[G2[mrg[agr1 agr2]]]].
    move:(merge_re_re mrg)=>[_[e1 e2]].
    exists G1.
    exists G2.
    repeat split...
    apply: agree_subst_wkU... by rewrite e1.
    apply: agree_subst_wkU... by rewrite e2. }
  move=>Δ1 Δ2 Δ σ Γ n A mrg agr ih tyn Γ1 Γ2 mrgL. inv mrgL.
  { move:(ih _ _ H2)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(merge_splitL mrg mrg1)=>[G3[mrg2 mrg3]].
    exists G3. exists G2... }
  { move:(ih _ _ H2)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(merge_splitR mrg mrg1)=>[G3[mrg2 mrg3]].
    exists G1. exists G3... }
  move=>Δ σ Γ n agr ih Γ1 Γ2 mrg. inv mrg.
  { move:(ih _ _ H2)=>[G1[G2[mrg1[agr1 agr2]]]].
    exists G1. exists G2... }
  move=>Δ σ Γ A B s l sb tyB1 tyB2 agr ih Γ1 Γ2 mrg. inv mrg.
  { have/ih[G1[G2[mrg[agr1 agr2]]]] : A :U Γ0 ∘ A :U Γ3 => A :U Γ...
    move:(merge_re_re mrg)=>[_[gd1 gd2]].
    move:(merge_re_re H2)=>[_[g0 g3]].
    exists G1. exists G2.
    repeat split...
    apply: agree_subst_conv...
    rewrite gd1...
    rewrite g0...
    apply: agree_subst_conv...
    rewrite gd2...
    rewrite g3... }
  { have/ih[G1[G2[mrg[agr1 agr2]]]] : A :L Γ0 ∘ _: Γ3 => A :L Γ...
    move:(merge_re_re mrg)=>[_[gd1 gd2]].
    move:(merge_re_re H2)=>[_[g0 g3]].
    exists G1. exists G2.
    repeat split...
    apply: agree_subst_conv...
    rewrite gd1...
    rewrite g0... }
  { have/ih[G1[G2[mrg[agr1 agr2]]]] : _: Γ0 ∘ A :L Γ3 => A :L Γ...
    move:(merge_re_re mrg)=>[_[gd1 gd2]].
    move:(merge_re_re H2)=>[_[g0 g3]].
    exists G1. exists G2.
    repeat split...
    apply: agree_subst_conv...
    rewrite gd2...
    rewrite g3... }
Qed.

Lemma arity_subst s l A σ : arity s l A -> arity s l A.[σ].
Proof with eauto using arity. move=>ar. elim: ar σ... Qed.

Definition n_subst σ x :=
  (forall i, ~x = i -> noccurs x (σ i)) /\ σ x = Var x.

Lemma noccurs_ren0 x m ξ :
  (forall i, ~ξ i = x) -> noccurs x m.[ren ξ].
Proof with eauto using noccurs, All1.
  move: m x ξ. apply: term_ind_nested...
  move=>A B s r t ihA ihB x ξ h. asimpl.
  { constructor...
    apply: ihB.
    move=>[|i]; asimpl... }
  move=>A m s t ihA ihm x ξ h. asimpl.
  { constructor...
    apply: ihm.
    move=>[|i]; asimpl... }
  move=>A Cs s ihA ihCs x ξ h. asimpl.
  { constructor...
    elim: ihCs...
    move=>C Cs' hd tl ih.
    constructor...
    apply: hd.
    move=>[|i]; asimpl... }
  move=>m Q Fs ihm ihQ ihFs x ξ h. asimpl.
  { constructor...
    elim: ihFs... }
  move=>k A m ihA ihm x ξ h. asimpl.
  { constructor...
    apply: ihm...
    move=>[|i]; asimpl... }
Qed.

Lemma n_subst0 σ : n_subst (up σ) 0.
Proof.
  split; eauto.
  move=> i. elim: i σ=>//=.
  move=> i _ σ _; asimpl.
  apply: noccurs_ren0; eauto.
Qed.

Lemma noccurs_up x m ξ :
  noccurs x m -> (forall i, ~x = i -> ~ξ x = ξ i) -> noccurs (ξ x) m.[ren ξ].
Proof with eauto using noccurs.
  move=> no. move: x m no ξ.
  apply: noccurs_ind_nested=>//=...
  move=>x A B s r t nA ihA nB ihB ξ h.
  { constructor...
    asimpl.
    apply: ihB.
    move=>[|i] h1; asimpl...
    move=>h2.
    have /h h3: ~x = i by eauto.
    eauto. }
  move=>x A m s t nA ihA nm ihm ξ h.
  { constructor...
    asimpl.
    apply: ihm.
    move=>[|i] h1; asimpl...
    move=>h2.
    have /h h3: ~x = i by eauto.
    eauto. }
  move=>x A Cs s nA ihA nCs ihCs ξ h.
  { constructor...
    elim: ihCs. constructor.
    move=>C Cs' hd tl ih.
    constructor...
    asimpl.
    apply: hd.
    move=>[|i] neq; asimpl...
    have /h h1: ~x = i by eauto.
    eauto. }
  move=>x m Q Fs nm ihm nQ ihQ nFs ihFs ξ h.
  { constructor...
    elim: ihFs. constructor.
    move=>F Fs' hd tl ih.
    constructor... }
  move=>x k A m nA ihA nm ihm ξ h.
  { constructor...
    asimpl.
    apply: ihm.
    move=>[|i] neq; asimpl...
    have /h h1: ~x = i by eauto.
    eauto. }
Qed.

Lemma n_subst_up σ x : n_subst σ x -> n_subst (up σ) x.+1.
Proof.
  move=>[h e]; split; asimpl.
  elim; asimpl.
  constructor; eauto.
  move=> n h' neq.
  have pf : ~x = n by eauto.
  move: (h _ pf)=>{}h.
  apply: noccurs_up; eauto.
  rewrite e. autosubst.
Qed.

Lemma noccurs_subst σ m x : noccurs x m -> n_subst σ x -> noccurs x m.[σ].
Proof with eauto using noccurs.
  move=>no. move: x m no σ.
  apply: noccurs_ind_nested=>//=...
  move=>x y neq σ [n _]...
  move=>x A B s r t nA ihA nB ihB σ no.
  { constructor...
    apply: ihB.
    apply: n_subst_up... }
  move=>x A m s t nA ihA nm ihm σ no.
  { constructor...
    apply: ihm.
    apply: n_subst_up... }
  move=>x A Cs s nA ihA nCs ihCs σ no.
  { constructor...
    elim: ihCs. constructor.
    move=>C Cs' hd tl ih.
    constructor...
    apply: hd.
    apply: n_subst_up... }
  move=>x m Q Fs nm ihm nQ ihQ nFs ihFs σ no.
  { constructor...
    elim: ihFs. constructor.
    move=>F Fs' hd tl ih.
    constructor... }
  move=>x k A m nA ihA nm ihm σ no.
  { constructor...
    apply: ihm.
    apply: n_subst_up... }
Qed.

Lemma pos_subst i A σ : pos i A -> n_subst σ i -> pos i A.[σ].
Proof with eauto.
  move=>p. elim: p σ=>//={i A}.
  move=>x ms ih σ [n e].
  rewrite spine_subst; asimpl.
  rewrite e.
  constructor.
  elim: ih. constructor.
  move=>m ms' hd tl ih. asimpl.
  constructor...
  apply: noccurs_subst...
  split...
  move=>x A B s r t tnA pB ihB σ no.
  constructor.
  apply: noccurs_subst...
  apply: ihB.
  apply: n_subst_up...
Qed.

Lemma constr_subst i s m σ :
  constr i s m -> n_subst σ i -> constr i s m.[σ].
Proof with eauto.
  move=>c. elim: c σ=>//={i m s}.
  move=>x s ms nms σ [n e].
  { rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: nms. constructor.
    move=>m ms' hd tl ih.
    constructor...
    apply: noccurs_subst...
    split... }
  move=>s t x A B leq pA nB cB ihB σ no.
  { apply: constr_pos...
    apply: pos_subst...
    apply: noccurs_subst...
    apply: n_subst0.
    apply: ihB.
    apply: n_subst_up... }
  move=>s t x A B leq nA cB ihB σ no.
  { apply: constr_pi...
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up... }
Qed.

Lemma rearity_subst k s s' l I A σ :
  arity s l A -> (rearity k s' I A).[σ] = rearity k s' I.[σ] A.[σ].
Proof.
  move=>ar. elim: ar I σ=>//={A}.
  move=>I σ.
  destruct k; asimpl=>//.
  move=>A B ar ih I σ.
  rewrite ih.
  by asimpl.
Qed.

Lemma respine0_I_subst Q I σ :
  (forall Q, respine0 Q I = Q) -> (forall x, ~I = Var x) -> Q.[σ] = respine0 Q.[σ] I.[σ].
Proof.
  elim: I σ=>//=.
  move=>x σ _ h.
  have//:=h x.
  move=>A _ B _ σ h _.
  have//:=h (Var 0).
Qed.

Lemma respine_I_subst k s s' Q c I σ :
  (forall Q c, respine k s Q c I = (s', kapp k Q c)) ->
  (forall x, ~I = Var x) ->
  s' = (respine k s Q.[σ] c.[σ] I.[σ]).1 /\
  kapp k Q.[σ] c.[σ] = (respine k s Q.[σ] c.[σ] I.[σ]).2.
Proof.
  elim: I k s s' Q c σ=>//=.
  move=>x k s s' Q c σ _ h. have//:=h x.
  move=>s l k s0 s' Q c σ h _.
  { have{}h:=h Q c.
    destruct k=>//=.
    inv h=>//.
    inv h=>//. }
  move=>A _ B _ s r t k s0 s' Q c σ h _.
  { have{h}:=h (Var 0) c.
    destruct k=>//=.
    destruct (respine U s0 (ids 1) (App c.[ren (+1)] (Var 0)) B)=>//.
    destruct (respine L s0 (ids 1) (App c.[ren (+1)] (Var 0)) B)=>//. }
  move=>A _ m _ s t k s0 s' Q c σ h _.
  { have{}h:=h (Var 0) c.
    destruct k=>//=.
    inv h=>//.
    inv h=>//. }
  move=>m _ n _ k s s' Q c σ h _.
  { have{}h:=h (Var 0) c.
    destruct k=>//=. }
  move=>A _ Cs s k s0 s' Q c σ h _.
  { have{}h:=h (Var 0) c.
    destruct k=>//=.
    inv h=>//.
    inv h=>//. }
  move=>i m _ t k s s' Q c σ h _.
  { have{}h:=h (Var 0) c.
    destruct k=>//=.
    inv h=>//.
    inv h=>//. }
  move=>m _ Q _ Fs k s s' Q0 c σ h _.
  { have{}h:=h (Var 0) c.
    destruct k=>//=.
    inv h=>//.
    inv h=>//. }
  move=>k0 A _ m _ k s s' Q c σ h _.
  { have{}h:=h (Var 0) c.
    destruct k=>//=.
    inv h=>//.
    inv h=>//. }
  move=>l k s s' Q c σ h _.
  { have{}h:=h (Var 0) c.
    destruct k=>//=.
    inv h=>//.
    inv h=>//. }
Qed.

Lemma kapp_subst k m n σ : (kapp k m n).[σ] = kapp k m.[σ] n.[σ].
Proof. destruct k=>//=. Qed.

Lemma respine0_spine'_I_subst Q I ms σ :
  (forall Q, respine0 Q I = Q) ->
  (forall x, ~I = Var x) ->
  (respine0 Q (spine' I ms)).[σ] = respine0 Q.[σ] (spine' I ms).[σ].
Proof.
  elim: ms Q I σ=>//=.
  move=>Q I σ h1 h2.
  rewrite h1.
  by apply: respine0_I_subst.
  move=>m ms ih Q I σ h1 h2.
  by rewrite ih.
Qed.

Lemma respine_spine'_I_subst k s s' Q c I ms σ :
  (forall Q c, respine k s Q c I = (s', kapp k Q c)) ->
  (forall x, ~I = Var x) ->
  (respine k s Q c (spine' I ms)).1 =
    (respine k s Q.[σ] c.[σ] (spine' I ms).[σ]).1 /\
  (respine k s Q c (spine' I ms)).2.[σ] =
    (respine k s Q.[σ] c.[σ] (spine' I ms).[σ]).2.
Proof.
  elim: ms Q I σ=>//=.
  move=>Q I σ h1 h2.
  rewrite h1=>//=.
  rewrite kapp_subst.
  by apply: respine_I_subst.
  move=>m ms ih Q I σ h1 h2.
  destruct k=>//=.
  rewrite respine0_spine'_I_subst; eauto.
  by apply: respine_respine0.
  rewrite respine0_spine'_I_subst; eauto.
  by apply: respine_respine0.
  Unshelve. all: eauto.
Qed.

Lemma respine_spine_I_subst k s s' I :
  (forall Q c, respine k s Q c I = (s', kapp k Q c)) ->
  (forall x, ~I = Var x) ->
  forall Q c ms σ,
    (respine k s Q c (spine I ms)).1 =
      (respine k s Q.[σ] c.[σ] (spine I ms).[σ]).1 /\
    (respine k s Q c (spine I ms)).2.[σ] =
      (respine k s Q.[σ] c.[σ] (spine I ms).[σ]).2.
Proof.
  move=>h1 h2 Q c ms σ.
  rewrite spine_spine'_rev.
  by apply: respine_spine'_I_subst.
Qed.

Lemma ren_var_false (I : var -> term) x :
  (forall y, ~I x = Var y) -> (forall y, ~(I x).[ren (+1)] = Var y).
Proof.
  move e:(I x)=> n h y.
  elim: n h I e y; intros; try discriminate.
  destruct y; asimpl.
  discriminate.
  move: (h y)=>{}h eq.
  inv eq.
  apply: h; eauto.
Qed.

Lemma constr_respine_subst x s' C :
  constr x s' C ->
  forall A Cs I,
    I x = Ind A Cs s' ->
    (forall y, ~I x = Var y) ->
  forall Q c k s σ,
    (respine k s Q c C.[I]).1 =
      (respine k s Q.[σ] c.[σ] C.[I].[σ]).1 /\
    (respine k s Q c C.[I]).2.[σ] =
      (respine k s Q.[σ] c.[σ] C.[I].[σ]).2.
Proof.
  move=>cn. elim: cn=>{x s' C}.
  move=>x s ms nms A Cs I h1 h2 Q c k s' σ.
  { rewrite!spine_subst. asimpl.
    have h: forall Q c, respine k s' Q c (I x) = (s', kapp k Q c).
    { move=>Q0 c0. rewrite h1.
      destruct k; simpl; eauto. }
    pose proof (respine_spine_I_subst h h2 Q c ms..[I] σ) as X.
    rewrite!spine_subst in X.
    by asimpl in X. }
  move=>s t x A B leq pA nB cB ih A0 Cs I h1 h2 Q c k s0 σ.
  { asimpl.
    have {}h1: up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] s.
    { asimpl. rewrite h1. autosubst. }
    have {}h2: forall y, ~up I x.+1 = Var y.
    { move=>y; asimpl.
      by apply: ren_var_false. }
    pose proof (ih _ _ _ h1 h2 Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) k s0 (up σ)) as hx.
    asimpl in hx.
    replace (Var 0) with (ids 0) in hx by autosubst.
    replace (Var 0) with (ids 0) by autosubst.
    remember (respine k s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as p1.
    remember (respine k s0 Q.[σ >> ren (+1)] (App c.[σ >> ren (+1)] (ids 0))
       B.[ids 0 .: I >> (σ >> ren (+1))]) as p2.
    destruct p1. destruct p2.
    split; eauto.
    asimpl. simpl in hx. destruct hx.
    repeat f_equal; eauto. }
  move=>s t x A B leq nA cB ih A0 Cs I h1 h2 Q c k s0 σ.
  { asimpl.
    have {}h1: up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] s.
    { asimpl. rewrite h1. autosubst. }
    have {}h2: forall y, ~up I x.+1 = Var y.
    { move=>y; asimpl.
      by apply: ren_var_false. }
    pose proof (ih _ _ _ h1 h2 Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) k s0 (up σ)) as hx.
    asimpl in hx.
    replace (Var 0) with (ids 0) in hx by autosubst.
    replace (Var 0) with (ids 0) by autosubst.
    remember (respine k s0 Q.[ren (+1)] (App c.[ren (+1)] (ids 0)) B.[up I]) as p1.
    remember (respine k s0 Q.[σ >> ren (+1)] (App c.[σ >> ren (+1)] (ids 0))
       B.[ids 0 .: I >> (σ >> ren (+1))]) as p2.
    destruct p1. destruct p2.
    split; eauto.
    asimpl. simpl in hx. destruct hx.
    repeat f_equal; eauto. }
Qed.

Lemma All2i_case_subst Γ Δ n k s s' A Q Fs Cs Cs' σ:
  All2i (fun i F C =>
    constr 0 s C /\
    let I := Ind A Cs' s in
    let T := mkcase k s' I Q (Constr i I s) C in
    forall Δ σ, Δ ⊢ σ ⊣ Γ ->
      Δ ⊢ F.[σ] : T.2.[σ] : T.1) n Fs Cs ->
  Δ ⊢ σ ⊣ Γ ->
  All2i (fun i F C =>
    constr 0 s C /\
    let I := Ind A.[σ] Cs'..[up σ] s in
    let T := mkcase k s' I Q.[σ] (Constr i I s) C in
    Δ ⊢ F : T.2 : T.1) n Fs..[σ] Cs..[up σ].
Proof.
  elim: Fs Γ Δ n s A Q Cs σ=>//=.
  move=>Γ Δ n s A Q Cs σ h agr. inv h.
  { constructor. }
  move=>F Fs ih Γ Δ n s A Q Cs σ h agr.
  inv h. inv H2.
  constructor.
  { split.
    asimpl.
    apply: constr_subst; eauto. apply: n_subst0.
    have{H0}tyF:=H0 _ _ agr.
    unfold mkcase in tyF.
    have h1: ((Ind A Cs' s .: ids) 0) = Ind A Cs' s by autosubst.
    have h2: ∀ x, ~(Ind A Cs' s .: ids) 0 = Var x.
    { move=>//. }
    have {h1 h2}[e1 e2]:=constr_respine_subst H h1 h2 Q (Constr n (Ind A Cs' s) s) k s' σ.
    rewrite e1 in tyF=>{e1}.
    rewrite e2 in tyF=>{e2}.
    asimpl in tyF.
    unfold mkcase.
    asimpl. eauto. }
  { apply: ih; eauto. }
Qed.

Lemma esubstitution Γ m A Δ s σ :
  Γ ⊢ m : A : s -> Δ ⊢ σ ⊣ Γ -> Δ ⊢ m.[σ] : A.[σ] : s.
Proof with eauto using agree_subst, agree_subst_re, agree_subst_key.
  move=>ty. move: Γ m A s ty Δ σ.
  apply: clc_type_ind_nested.
  move=>Γ s l k Δ σ agr. asimpl.
  { apply: clc_axiom... }
  move=>Γ A B s r t i k tyA ihA tyB ihB Δ σ agr. asimpl.
  { apply: clc_pi... }
  move=>Γ x A s hs Δ σ agr. asimpl.
  { apply: agree_subst_has... }
  move=>Γ A B m s r t i k tyP ihP tym ihm Δ σ agr. asimpl.
  { apply: clc_lam... }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn Δ σ agr. asimpl.
  { move:(merge_agree_subst_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    replace B.[n.[σ] .: σ] with B.[up σ].[n.[σ]/] by autosubst.
    move:(agree_subst_key agr2 k)=>{}k.
    apply: clc_app... }
  move=>Γ A Cs s l1 l2 k ar ctr tyA ihA tyCs ihCs Δ σ agr. asimpl.
  { asimpl.
    apply: clc_indd...
    apply: arity_subst...
    move=>{agr}.
    elim: ctr σ=>//=...
    { move=>_. constructor. }
    { move=>m ls c h ih σ. asimpl.
      constructor.
      apply: constr_subst... apply: n_subst0.
      have:=ih σ... }
    elim: ihCs=>//=.
    { constructor. }
    { move=>m ls ihm hls ihls. asimpl.
      constructor... } }
  move=>Γ A s i C Cs//=k ig ty ih Δ σ agr.
  { replace (C.[Ind A Cs s/].[σ])
      with (C.[up σ]).[Ind A.[σ] Cs..[up σ] s/] by autosubst.
    apply: clc_constr...
    apply: iget_subst... }
  move=>Γ1 Γ2 Γ A Q s s' l//=k Fs Cs m ms leq ar key mrg tym ihm tyQ ihQ tyFs ihFs Δ σ agr.
  { rewrite kapp_subst.
    rewrite spine_subst.
    have[G1[G2[mrg'[agr1 agr2]]]]:=merge_agree_subst_inv agr mrg.
    have ar':=arity_subst σ ar.
    have{}ihm:=ihm _ _ agr1. rewrite spine_subst in ihm.
    have{}ihQ:=ihQ _ _ (agree_subst_re agr2).
    rewrite (rearity_subst k s' (Ind A Cs s) σ ar) in ihQ.
    apply: clc_case.
    apply: leq.
    eauto.
    apply: agree_subst_key.
    apply: agr1.
    all: eauto.
    apply: All2i_case_subst; eauto. }
  move=>Γ k0 A m l k tyA ihA tym ihm Δ σ agr.
  { asimpl.
    apply: clc_fix.
    apply: agree_subst_key; eauto.
    apply: ihA; eauto.
    replace A.[σ].[ren (+1)] with A.[ren (+1)].[up σ]
      by autosubst.
    apply: ihm.
    by constructor. }
  move=>Γ A B m s i sb tym ihm tyB ihB Δ σ agr.
  { apply: clc_conv.
    apply: sub_subst...
    apply: ihm...
    apply: ihB... }
Qed.

Lemma substitution Γ1 Γ2 Γ m n A B s t :
  A :{s} Γ1 ⊢ m : B : t ->
  Γ2 |> s ->
  Γ1 ∘ Γ2 => Γ -> 
  Γ2 ⊢ n : A : s -> 
  Γ ⊢ m.[n/] : B.[n/] : t.
Proof with eauto.
  move=>tym k mrg tyn.
  apply: esubstitution...
  destruct s.
  { apply: agree_subst_wkU.
    move:(merge_pureR mrg k)=>->...
    move:(merge_re_re mrg)=>[_[_<-]].
    rewrite<-pure_re...
    by asimpl. }
  { apply: agree_subst_wkL...
    by asimpl. }
Qed.

Lemma substitutionN Γ1 Γ2 m n A B s t :
  _: Γ1 ⊢ m : B : s -> Γ2 ⊢ n : A : t -> Γ1 ⊢ m.[n/] : B.[n/] : s.
Proof with eauto.
  move=>tym tyn.
  apply: esubstitution...
  apply: agree_subst_wkN...
Qed.

Lemma strengthen Γ m A s :
  _: Γ ⊢ m.[ren (+1)] : A.[ren (+1)] : s -> Γ ⊢ m : A : s.
Proof with eauto using key.
  move=>tym.
  have ty : (nil ⊢ U @ 0 : U @ 1 : U).
  apply: clc_axiom...
  have := (substitutionN tym ty).
  by asimpl.
Qed.

Lemma context_conv Γ m A B C s t l :
  B === A -> 
  [Γ] ⊢ A : s @ l : U -> A :{s} Γ ⊢ m : C : t -> B :{s} Γ ⊢ m : C : t.
Proof with eauto.
  move=>conv tpA tpm.
  cut (B :{s} Γ ⊢ m.[ids] : C.[ids] : t). autosubst.
  apply: esubstitution...
  apply: agree_subst_conv.
  apply: conv_sub...
  destruct s=>//=; asimpl.
  apply: eweakeningU; eauto.
  asimpl; eauto.
  apply: eweakeningN; eauto.
  asimpl; eauto.
  eauto.
  apply: agree_subst_refl.
Qed.
