From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope sort_scope.
Delimit Scope sort_scope with srt.
Open Scope sort_scope.

Inductive sort : Type := U | L.
Bind Scope sort_scope with sort.

Definition elem T := option (T * sort).
Definition context T := seq (elem T).

Notation "m :U Γ" := (Some (m, U) :: Γ) 
  (at level 30, right associativity).
Notation "m :L Γ" := (Some (m, L) :: Γ) 
  (at level 30, right associativity).
Notation "m :{ s } Γ" := (Some (m, s) :: Γ) 
  (at level 30, right associativity, format "m  :{ s }  Γ").
Notation "_: Γ" := (None :: Γ) 
  (at level 30, right associativity).

Definition sort_plus (s t : sort) :=
  match s with
  | U => t
  | L => L
  end.
Infix "⋅" := sort_plus (at level 30) : sort_scope.

Inductive sort_leq : sort -> sort -> Prop :=
| sort_leqU s :
  sort_leq U s
| sort_leqL :
  sort_leq L L.
Infix "≤" := sort_leq : sort_scope.

Reserved Notation "Γ1 ∘ Γ2 => Γ" (at level 40).
Inductive merge T : context T -> context T -> context T -> Prop :=
| merge_nil :
  nil ∘ nil => nil
| merge_left Γ1 Γ2 Γ m : 
  Γ1 ∘ Γ2 => Γ ->
  m :U Γ1 ∘ m :U Γ2 => m :U Γ
| merge_right1 Γ1 Γ2 Γ m :
  Γ1 ∘ Γ2 => Γ ->
  m :L Γ1 ∘ _: Γ2 => m :L Γ
| merge_right2 Γ1 Γ2 Γ m :
  Γ1 ∘ Γ2 => Γ ->
  _: Γ1 ∘ m :L Γ2 => m :L Γ
| merge_null Γ1 Γ2 Γ :
  Γ1 ∘ Γ2 => Γ ->
  _: Γ1 ∘ _: Γ2 => _: Γ
where "Γ1 ∘ Γ2 => Γ" := (merge Γ1 Γ2 Γ).

Reserved Notation "Γ |> s" (at level 40).
Inductive key T : context T -> sort -> Prop :=
| key_nil s :
  nil |> s
| key_u Γ m :
  Γ |> U ->
  m :U Γ |> U
| key_l Γ m s :
  Γ |> L ->
  m :{s} Γ |> L
| key_n Γ s :
  Γ |> s ->
  _: Γ |> s
where "Γ |> s" := (key Γ s).

Inductive has {T} `{Ids T} `{Subst T} :
  context T -> var -> sort -> T -> Prop :=
| has_O Γ A s :
  Γ |> U ->
  has (A :{s} Γ) 0 s A.[ren (+1)]
| has_S Γ A B x s :    
  has Γ x s A ->
  has (B :U Γ) x.+1 s A.[ren (+1)]
| has_N Γ A x s :
  has Γ x s A ->
  has (_: Γ) x.+1 s A.[ren (+1)].

Fixpoint re T (Γ : context T) : context T :=
  match Γ with
  | Some (m, U) :: Γ => Some (m, U) :: re Γ
  | _ :: Γ => None :: re Γ
  | _ => nil
  end.
Notation "[ Γ ]" := (re Γ).

Lemma key_impure T (Γ : context T) : Γ |> L.
Proof with eauto using key.
  elim: Γ...
  move=>[[A s]|] Γ k...
Qed.

Lemma has_size {T}  `{Ids T} `{Subst T} (Γ : context T) x s A :
  has Γ x s A -> x < size Γ.
Proof. elim=>//{Γ x s A}. Qed.

Lemma re_size T (Γ : context T) : size Γ = size [Γ].
Proof.
  elim: Γ=>//.
  move=>[[x[|]]|] Γ e//=.
  by rewrite e.
  by rewrite e.
  by rewrite e.
Qed.

Lemma merge_size T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> 
  size Γ1 = size Γ /\ size Γ2 = size Γ.
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=>Γ1 Γ2 Γ m mrg [->->]//.
  move=>Γ1 Γ2 Γ m mrg [->->]//.
  move=>Γ1 Γ2 Γ m mrg [->->]//.
  move=>Γ1 Γ2 Γ mrg [->->]//.
Qed.

Lemma merge_sym T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> Γ2 ∘ Γ1 => Γ.
Proof.
  elim; move=>*; eauto using merge.
Qed.

Lemma merge_pure T (Γ : context T) :
  Γ |> U -> Γ ∘ Γ => Γ.
Proof.
  move e:(U)=> s k.
  elim: k e; move=>//=*; eauto using merge.
Qed.

Lemma merge_reL T (Γ : context T) :
  [Γ] ∘ Γ => Γ.
Proof.
  elim: Γ; eauto using merge.
  move=> [[A[|]]|] Γ mrg//=; eauto using merge.
Qed.

Lemma merge_reR T (Γ : context T) :
  Γ ∘ [Γ] => Γ.
Proof.
  elim: Γ; eauto using merge.
  move=> [[A[|]]|] Γ mrg//=; eauto using merge.
Qed.

Lemma merge_pure_inv T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> Γ |> U -> Γ1 |> U /\ Γ2 |> U.
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
    firstorder; eauto using key.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
  move=> Γ1 Γ2 Γ mrg1 ih mrg2.
    inv mrg2.
    firstorder; eauto using key.
Qed.

Lemma pure_split T (Γ : context T) :
  Γ |> U -> exists Γ1 Γ2, Γ1 |> U /\ Γ2 |> U /\ Γ1 ∘ Γ2 => Γ.
Proof with eauto using merge, key.
  move e:(U)=>s k. elim: k e=>//{Γ s}.
  move=>s e; subst.
    exists nil. exists nil...
  move=>Γ m k ih _.
    have[G1[G2[k1[k2 mrg]]]]:=ih erefl.
    exists (m :U G1). exists (m :U G2).
    repeat split...
  move=>Γ s k ih e; subst.
    have[G1[G2[k1[k2 mrg]]]]:=ih erefl.
    exists (_: G1). exists (_: G2).
    repeat split...
Qed.

Lemma merge_pureL T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> Γ1 |> U -> Γ = Γ2.
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
    by rewrite ih.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
    by rewrite ih.
  move=> Γ1 Γ2 Γ mrg1 ih mrg2.
    inv mrg2.
    by rewrite ih.
Qed.

Lemma merge_pureR T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> Γ2 |> U -> Γ = Γ1.
Proof.
  move/merge_sym. exact: merge_pureL.
Qed.

Lemma merge_key T (Γ1 Γ2 Γ : context T) s :
  Γ1 ∘ Γ2 => Γ -> Γ1 |> s -> Γ2 |> s -> Γ |> s.
Proof.
  move=>mrg. elim: mrg s=>//={Γ1 Γ2 Γ}.
  move=>Γ1 Γ2 Γ m mrg ih [|] k1 k2. 
    inv k1. inv k2. constructor; eauto.
    inv k1. inv k2. constructor; eauto.
  move=>Γ1 Γ2 Γ m mrg ih [|] k1 k2. 
    inv k1. inv k1. inv k2. constructor; eauto.
  move=>Γ1 Γ2 Γ m mrg ih [|] k1 k2. 
    inv k2. inv k1. inv k2. constructor; eauto.
  move=>Γ1 Γ2 Γ mrg ih [|] k1 k2.
    inv k1. inv k2. constructor; eauto.
    inv k1. inv k2. constructor; eauto.
Qed.

Lemma merge_key_sum T (Γ1 Γ2 Γ : context T) s r t :
  Γ1 ∘ Γ2 => Γ -> Γ1 |> s -> Γ2 |> r -> s ⋅ r ≤ t -> Γ |> t.
Proof with eauto using key, key_impure, sort_leq.
  move=>mrg. elim: mrg s r t=>//={Γ1 Γ2 Γ}...
  move=>G1 G2 G m mrg ih s r t k1 k2 le.
  { inv k1; inv k2; destruct t; inv le... }
  move=>G1 G2 G m mrg ih s r t k1 k2 le.
  { inv k1; inv k2; destruct t; inv le... }
  move=>G1 G2 G m mrg ih s r t k1 k2 le.
  { inv k1; inv k2; destruct t; inv le... 
    destruct s. inv H1. inv H1. }
  move=>G1 G2 G mrg ih s r t k1 k2 le.
  { inv k1; inv k2; destruct t; inv le... 
    destruct s; destruct r; inv H2... }
Qed.

Lemma merge_pure_pure T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> Γ1 |> U -> Γ2 |> U -> Γ |> U.
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=> Γ1 Γ2 Γ A mrg ih k1 k2.
    inv k1. inv k2.
    by eauto using key.
  move=> Γ1 Γ2 Γ A mrg ih k.
    by inv k.
  move=> Γ1 Γ2 Γ A mrg ih _ k.
    by inv k.
  move=> Γ1 Γ2 Γ mrg ih k1 k2.
    inv k1. inv k2.
    by eauto using key.
Qed.

Lemma merge_impureL T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> Γ1 |> L -> Γ |> L.
Proof with eauto using key.
  elim=>{Γ1 Γ2 Γ}...
  move=>Γ1 Γ2 Γ m mrg ih k. inv k...
  move=>Γ1 Γ2 Γ m mrg ih k. inv k...
  move=>Γ1 Γ2 Γ m mrg ih k. inv k...
  move=>Γ1 Γ2 Γ mrg ih k. inv k...
Qed.

Lemma merge_impureR T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> Γ2 |> L -> Γ |> L.
Proof with eauto using key.
  move/merge_sym.
  exact: merge_impureL.
Qed.

Lemma merge_pure_eq T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> Γ1 |> U -> Γ2 |> U -> Γ1 = Γ /\ Γ2 = Γ.
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=> Γ1 Γ2 Γ A mrg ih k1 k2.
    inv k1. inv k2.
    have[e1 e2]:=ih H0 H1.
    split.
    by rewrite e1.
    by rewrite e2.
  move=> Γ1 Γ2 Γ A _ _ k.
    inv k.
  move=> Γ1 Γ2 Γ A _ _ _ k.
    inv k.
  move=> Γ1 Γ2 Γ mrg ih k1 k2.
    inv k1. inv k2.
    have[e1 e2]:=ih H0 H1.
    split.
    by rewrite e1.
    by rewrite e2.
Qed.

Lemma merge_re_re T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> [Γ1] = [Γ2] /\ [Γ1] = [Γ] /\ [Γ2] = [Γ].
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=> Γ1 Γ2 Γ A mrg[->[->_]]//.
  move=> Γ1 Γ2 Γ A mrg[->[->_]]//.
  move=> Γ1 Γ2 Γ A mrg[->[->_]]//.
  move=> Γ1 Γ2 Γ mrg[->[->_]]//.
Qed.

Lemma merge_re_id T (Γ : context T) :
  [Γ] ∘ [Γ] => [Γ].
Proof.
  elim: Γ; eauto using merge.
  move=> [[A[|]]|] Γ mrg; eauto using merge.
Qed.

Lemma merge_re3 T  (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ -> [Γ1] ∘ [Γ2] => [Γ].
Proof.
  move/merge_re_re=>[_[->->]].
  exact:merge_re_id.
Qed.

Lemma re_invo T (Γ : context T) : [Γ] = [[Γ]].
Proof.
  elim: Γ=>//.
  move=> [[A[|]]|] Γ//=<-//.
Qed.

Lemma pure_re T (Γ : context T) : Γ |> U -> Γ = [Γ].
Proof.
  elim: Γ=>//.
  move=> [[A[|]]|] Γ ih k//=.
  inv k. by rewrite<-ih.
  inv k.   
  inv k. by rewrite<-ih.
Qed.

Lemma re_pure T (Γ : context T) : [Γ] |> U.
Proof.
  elim: Γ; eauto using key.
  move=> [[A[|]]|] Γ k//=; eauto using key.
Qed.

Lemma re_sort T (Γ : context T) t : [Γ] |> t.
Proof with eauto using key.
  elim: Γ...
  move=> [[A[|]]|] Γ k//=...
  destruct t...
Qed.

Lemma hasU_re {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  has Γ x U A -> has [Γ] x U A.
Proof.
  move e:(U) => s h.
  elim: h e=>{Γ x s A}.
  move=> Γ A s k <-//=.
    constructor.
    by rewrite<-pure_re.
  move=> Γ A B x s h ih e//=; subst.
    by constructor; eauto.
  move=> Γ A x s h ih e//=; subst.
    by constructor; eauto.
Qed.

Lemma hasL_re {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  ~has [Γ] x L A.
Proof.
  elim: Γ x A.
  move=>//=x A h. inv h.
  move=>[[B[|]]|] Γ ih x A //=h.
  inv h. apply: ih; eauto.
  inv h. apply: ih; eauto.
  inv h. apply: ih; eauto.
Qed.

Lemma hasU_pure {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  has Γ x U A -> Γ |> U.
Proof.
  move e:(U)=>s h.
  elim: h e=>{Γ x A s}.
  move=> Γ A s ih <-; eauto using key.
  move=> Γ A B x s h ih e; subst; eauto using key.
  move=> Γ A x s h ih e; subst; eauto using key.
Qed.

Lemma hasL_pure {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  has Γ x L A -> ~ Γ |> U.
Proof.
  move e:(L)=>s h.
  elim: h e=>{Γ x A s}.
  move=> Γ A s k e contra; subst. inv contra.
  move=> Γ A B x s h ih e contra. 
    inv contra.
    by apply: ih.
  move=> Γ A x s h ih e contra.
    inv contra.
    by apply ih.
Qed.

Lemma has_inj {T} `{Ids T} `{Subst T} (Γ : context T) x s t A B :
  has Γ x s A -> has Γ x t B -> A = B /\ s = t.
Proof.
  move=> h.
  elim: h B t=>{Γ x s A}.
  move=> Γ A s k B t h.
    by inv h.
  move=> Γ A B x s hA ih B0 t hB.
    inv hB.
    by move:(ih _ _ H6)=>[->->]//.
  move=> Γ A x s hA ih B0 t hB.
    inv hB.
    by move:(ih _ _ H3)=>[->->]//.
Qed.

Lemma merge_splitL T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ ->
  forall Δ1 Δ2,
    Δ1 ∘ Δ2 => Γ1 ->
    exists Δ, 
      Δ1 ∘ Γ2 => Δ /\ Δ ∘ Δ2 => Γ.
Proof.
  elim=>{Γ1 Γ2 Γ}.
  move=> Δ1 Δ2 mrg. 
    inv mrg.
    exists nil.
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :U G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :L G).
    by eauto using merge.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (_: G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :L G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (_: G).
    by eauto using merge.
Qed.

Lemma merge_splitR T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ ->
  forall Δ1 Δ2,
    Δ1 ∘ Δ2 => Γ1 ->
    exists Δ,
      Δ2 ∘ Γ2 => Δ /\ Δ1 ∘ Δ => Γ.
Proof.
  elim=>{Γ1 Γ2 Γ}.
  move=> Δ1 Δ2 mrg. 
    inv mrg.
    exists nil.
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :U G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (_: G).
    by eauto using merge.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :L G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :L G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (_: G).
    by eauto using merge.
Qed.

Lemma merge_distr T (Γ1 Γ2 Γ : context T) :
  Γ1 ∘ Γ2 => Γ ->
  forall Δ11 Δ12 Δ21 Δ22,
    Δ11 ∘ Δ12 => Γ1 ->
    Δ21 ∘ Δ22 => Γ2 ->
    exists Δ1 Δ2,
      Δ1 ∘ Δ2 => Γ /\
      Δ11 ∘ Δ21 => Δ1 /\
      Δ12 ∘ Δ22 => Δ2.
Proof with eauto using merge.
  elim=>{Γ1 Γ2 Γ}.
  move=>D11 D12 D21 D22 mrg1 mrg2.
    inv mrg1. inv mrg2.
    exists nil. exists nil...
  move=>G1 G2 G m mrg ih D11 D12 D21 D22 mrg1 mrg2.
    inv mrg1. inv mrg2.
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (m :U D1). exists (m :U D2).
    repeat split...
  move=>G1 G2 G m mrg ih D11 D12 D21 D22 mrg1 mrg2.
    inv mrg1; inv mrg2.
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (m :L D1). exists (_: D2). repeat split...
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (_: D1). exists (m :L D2). repeat split...
  move=>G1 G2 G m mrg ih D11 D12 D21 D22 mrg1 mrg2.
    inv mrg1; inv mrg2.
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (m :L D1). exists (_: D2). repeat split...
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (_: D1). exists (m :L D2). repeat split...
  move=>G1 G2 G mrg ih D11 D12 D21 D22 mrg1 mrg2.
    inv mrg1; inv mrg2.
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (_: D1). exists (_: D2). repeat split...
Qed.
