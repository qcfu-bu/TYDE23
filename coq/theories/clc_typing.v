(* This file defines the typing rules of CILC. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Arities *)
Inductive arity (s : sort) (l : nat) : term -> Prop :=
| arity_sort : arity s l (s @ l)
| arity_pi A B : arity s l B -> arity s l (Pi A B U U U).

(* noccurs x m asserts that x does not occur in term m. *)
Inductive noccurs : var -> term -> Prop :=
| noccurs_var x y : ~x = y -> noccurs x (Var y)
| noccurs_sort x s l : noccurs x (s @ l)
| noccurs_pi x A B s r t :
  noccurs x A -> noccurs x.+1 B -> noccurs x (Pi A B s r t)
| noccurs_lam x A m s t :
  noccurs x A -> noccurs x.+1 m -> noccurs x (Lam A m s t)
| noccurs_app x m n :
  noccurs x m -> noccurs x n -> noccurs x (App m n)
| noccurs_indd x A Cs s :
  noccurs x A -> All1 (noccurs x.+1) Cs -> noccurs x (Ind A Cs s)
| noccurs_constr x i m s :
  noccurs x m -> noccurs x (Constr i m s)
| noccurs_case x m Q Fs :
  noccurs x m -> noccurs x Q -> All1 (noccurs x) Fs -> noccurs x (Case m Q Fs)
| noccurs_fix x k A m :
  noccurs x A -> noccurs x.+1 m -> noccurs x (Fix k A m)
| noccurs_ptr x l : noccurs x (Ptr l).

(* Strengthen induction principle for noccurs to handle nested induction. *)
Section noccurs_ind_nested.
  Variable P : var -> term -> Prop.
  Hypothesis ih_var : forall x y, ~x = y -> P x (Var y).
  Hypothesis ih_sort : forall x s l, P x (s @ l).
  Hypothesis ih_pi : forall x A B s r t,
    noccurs x A -> P x A -> noccurs x.+1 B -> P x.+1 B -> P x (Pi A B s r t).
  Hypothesis ih_lam : forall x A m s t,
    noccurs x A -> P x A -> noccurs x.+1 m -> P x.+1 m -> P x (Lam A m s t).
  Hypothesis ih_app : forall x m n,
    noccurs x m -> P x m -> noccurs x n -> P x n -> P x (App m n).
  Hypothesis ih_indd : forall x A Cs s,
    noccurs x A -> P x A ->
    All1 (noccurs x.+1) Cs -> All1 (P x.+1) Cs ->
    P x (Ind A Cs s).
  Hypothesis ih_constr : forall x i m s,
    noccurs x m -> P x m -> P x (Constr i m s).
  Hypothesis ih_case : forall x m Q Fs,
    noccurs x m -> P x m ->
    noccurs x Q -> P x Q ->
    All1 (noccurs x) Fs -> All1 (P x) Fs ->
    P x (Case m Q Fs).
  Hypothesis ih_fix : forall x k A m,
    noccurs x A -> P x A ->
    noccurs x.+1 m -> P x.+1 m ->
    P x (Fix k A m).
  Hypothesis ih_ptr : forall x l, P x (Ptr l).

  Fixpoint noccurs_ind_nested x m (no : noccurs x m) : P x m.
  Proof.
    have ih_nestd :=
      fix fold x ls (no : All1 (noccurs x) ls) : All1 (P x) ls :=
        match no with
        | All1_nil => All1_nil _
        | All1_cons _ _ hd tl =>
          All1_cons (noccurs_ind_nested x _ hd) (fold x _ tl)
        end.
    case no; move=>*.
    apply: ih_var; eauto.
    apply: ih_sort; eauto.
    apply: ih_pi; eauto.
    apply: ih_lam; eauto.
    apply: ih_app; eauto.
    apply: ih_indd; eauto.
    apply: ih_constr; eauto.
    apply: ih_case; eauto.
    apply: ih_fix; eauto.
    apply: ih_ptr; eauto.
  Qed.
End noccurs_ind_nested.

(* Positivity condition. *)
Inductive pos : var -> term -> Prop :=
| pos_X x ms : All1 (noccurs x) ms -> pos x (spine (Var x) ms)
| pos_pi x A B s r t : noccurs x A -> pos x.+1 B -> pos x (Pi A B s r t).

(* Well-formed Constructors. *)
Inductive constr : var -> sort -> term -> Prop :=
| constr_X x s ms :
  All1 (noccurs x) ms ->
  constr x s (spine (Var x) ms)
| constr_pos s t x A B :
  t ≤ s ->
  pos x A ->
  noccurs 0 B ->
  constr x.+1 s B ->
  constr x s (Pi A B t s s)
| constr_pi s t x A B :
  t ≤ s ->
  noccurs x A ->
  constr x.+1 s B ->
  constr x s (Pi A B t s s).

(* The rearity function computes a motive type from arity A. *)
Fixpoint rearity (k s : sort) (I A : term) : term :=
  match A with
  | _ @ l =>
    match k with
    | U => Pi I (s @ l) U U U
    | L => s @ l
    end
  | Pi A B u v U =>
    Pi A (rearity k s (App I.[ren (+1)] (Var 0)) B) u v U
  | _ => A
  end.

Fixpoint respine0 hd sp :=
  match sp with
  | App m n => App (respine0 hd m) n
  | _ => hd
  end.

Fixpoint respine (k s : sort) hd c sp : (sort * term) :=
  match sp with
  | Pi A B u _ t =>
    let (v, B) := respine k s hd.[ren (+1)] (App c.[ren (+1)] (Var 0)) B in
    (L, Pi A B u v L)
  | _ =>
    match k with
    | U => (s, App (respine0 hd sp) c)
    | L => (s, respine0 hd sp)
    end
  end.

Definition r1 sp s := 
  match sp with
  | Pi _ _ _ _ _ => L
  | _ => s
  end.

(* r2 computes the branch type from a constructor type sp. *)
Fixpoint r2 (k s : sort) hd c sp := 
  match sp with
  | Pi A B u _ t =>
    Pi A (r2 k s hd.[ren (+1)] (App c.[ren (+1)] (Var 0)) B) u (r1 B s) L
  | _ =>
    match k with
    | U => App (respine0 hd sp) c
    | L => respine0 hd sp
    end
  end.

Lemma r2_respine k s hd c sp :
  respine k s hd c sp = (r1 sp s, r2 k s hd c sp).
Proof.
  move: k s hd c. elim: sp.
  move=>x [|] s hd c=>//=.
  move=>s l [|] r hd c=>//=.
  move=>A ihA B ihB s r t k s0 hd c=>//=.
    by rewrite ihB.
  move=>A _ m _ s t [|] s0 hd c =>//=.
  move=>m _ n _ [|] s hd c=>//=.
  move=>A _ Cs s [|] r hd c=>//=.
  move=>i m _ s [|] r hd c=>//=.
  move=>m _ Q _ Fs [|] s hd c=>//=.
  move=>k A _ m _ [|] s hd c=>//=.
  move=>l [|] s hd c=>//=.
Qed.

Definition mkcase k s I Q c C := respine k s Q c C.[I/].

(* Conditional Apply. *)
Definition kapp k m n :=
  match k with
  | U => App m n
  | L => m
  end.

Reserved Notation "Γ ⊢ m : A : s" 
  (at level 50, m, A, s at next level).

(* Typing rules for CILC.  *)
Inductive clc_type : context term -> term -> term -> sort -> Prop :=
| clc_axiom Γ s l :
  Γ |> U ->
  Γ ⊢ s @ l : U @ l.+1 : U
| clc_pi Γ A B s r t i :
  Γ |> U ->
  Γ ⊢ A : s @ i : U ->
  [A :{s} Γ] ⊢ B : r @ i : U ->
  Γ ⊢ Pi A B s r t : t @ i : U
| clc_var Γ x A s :
  has Γ x s A ->
  Γ ⊢ Var x : A : s
| clc_lam Γ A B m s r t i :
  Γ |> t ->
  [Γ] ⊢ Pi A B s r t : t @ i : U ->
  A :{s} Γ ⊢ m : B : r ->
  Γ ⊢ Lam A m s t : Pi A B s r t : t
| clc_app Γ1 Γ2 Γ A B m n s r t :
  Γ2 |> s ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Pi A B s r t : t ->
  Γ2 ⊢ n : A : s ->
  Γ ⊢ App m n : B.[n/] : r
| clc_indd Γ A Cs s l1 l2 :
  Γ |> U ->
  arity s l1 A ->
  All1 (constr 0 s) Cs ->
  Γ ⊢ A : U @ l2 : U ->
  All1 (fun C => A :U Γ ⊢ C : s @ l1 : U) Cs ->
  Γ ⊢ Ind A Cs s : A : U
| clc_constr Γ A s i C Cs :
  let I := Ind A Cs s in
  Γ |> U ->
  iget i Cs C ->
  Γ ⊢ I : A : U ->
  Γ ⊢ Constr i I s : C.[I/] : s
| clc_case Γ1 Γ2 Γ A Q s s' l k Fs Cs m ms :
  let I := Ind A Cs s in
  s ≤ k ->
  arity s l A ->
  Γ1 |> k ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : spine I ms : s ->
  [Γ2] ⊢ Q : rearity k s' I A : U ->
  All2i (fun i F C =>
    constr 0 s C /\
    let T := mkcase k s' I Q (Constr i I s) C in
    Γ2 ⊢ F : T.2 : T.1) 0 Fs Cs ->
  Γ ⊢ Case m Q Fs : kapp k (spine Q ms) m : s'
| clc_fix Γ k A m l :
  Γ |> U ->
  Γ ⊢ A : U @ l : U ->
  A :U Γ ⊢ m : A.[ren (+1)] : U ->
  Γ ⊢ Fix k A m : A : U
| clc_conv Γ A B m s i :
  A <: B ->
  Γ ⊢ m : A : s ->
  [Γ] ⊢ B : s @ i : U ->
  Γ ⊢ m : B : s
where "Γ ⊢ m : A : s" := (clc_type Γ m A s).

(* Strengthen induction principle for clc_type to handle nested induction. *)
Section clc_type_ind_nested.
  Variable P : context term -> term -> term -> sort -> Prop.
  Hypothesis ih_sort : forall Γ s l,
    Γ |> U -> P Γ (s @ l) (U @ l.+1) U.
  Hypothesis ih_pi : forall Γ A B s r t i,
    Γ |> U ->
    Γ ⊢ A : s @ i : U -> P Γ A (s @ i) U ->
    [A :{s} Γ] ⊢ B : r @ i : U -> P [A :{s} Γ] B (r @ i) U ->
    P Γ (Pi A B s r t) (t @ i) U.
  Hypothesis ih_var : forall Γ x A s,
    has Γ x s A -> P Γ (Var x) A s.
  Hypothesis ih_lam : forall Γ A B m s r t i,
    Γ |> t ->
    [Γ] ⊢ Pi A B s r t : t @ i : U -> P [Γ] (Pi A B s r t) (t @ i) U ->
    A :{s} Γ ⊢ m : B : r -> P (A :{s} Γ) m B r ->
    P Γ (Lam A m s t) (Pi A B s r t) t.
  Hypothesis ih_app : forall Γ1 Γ2 Γ A B m n s r t,
    Γ2 |> s ->
    Γ1 ∘ Γ2 => Γ ->
    Γ1 ⊢ m : Pi A B s r t : t -> P Γ1 m (Pi A B s r t) t ->
    Γ2 ⊢ n : A : s -> P Γ2 n A s ->
    P Γ (App m n) B.[n/] r.
  Hypothesis ih_indd : forall Γ A Cs s l1 l2,
    Γ |> U ->
    arity s l1 A ->
    All1 (constr 0 s) Cs ->
    Γ ⊢ A : U @ l2 : U -> P Γ A (U @ l2) U ->
    All1 (fun C => A :U Γ ⊢ C : s @ l1 : U) Cs ->
    All1 (fun C => P (A :U Γ) C (s @ l1) U) Cs ->
    P Γ (Ind A Cs s) A U.
  Hypothesis ih_constr : forall Γ A s i C Cs,
    let I := Ind A Cs s in
    Γ |> U ->
    iget i Cs C ->
    Γ ⊢ I : A : U -> P Γ I A U ->
    P Γ (Constr i I s) C.[I/] s.
  Hypothesis ih_case : forall Γ1 Γ2 Γ A Q s s' l k Fs Cs m ms,
    let I := Ind A Cs s in
    s ≤ k ->
    arity s l A ->
    Γ1 |> k ->
    Γ1 ∘ Γ2 => Γ ->
    Γ1 ⊢ m : spine I ms : s -> P Γ1 m (spine I ms) s ->
    [Γ2] ⊢ Q : rearity k s' I A : U -> P [Γ2] Q (rearity k s' I A) U ->
    All2i (fun i F C =>
      constr 0 s C /\
      let T := mkcase k s' I Q (Constr i I s) C in
      Γ2 ⊢ F : T.2 : T.1) 0 Fs Cs ->
    All2i (fun i F C =>
      constr 0 s C /\
      let T := mkcase k s' I Q (Constr i I s) C in
      P Γ2 F T.2 T.1) 0 Fs Cs ->
    P Γ (Case m Q Fs) (kapp k (spine Q ms) m) s'.
  Hypothesis ih_fix : forall Γ k A m l,
    Γ |> U ->
    Γ ⊢ A : U @ l : U -> P Γ A (U @ l) U ->
    A :U Γ ⊢ m : A.[ren (+1)] : U -> P (A :U Γ) m A.[ren (+1)] U ->
    P Γ (Fix k A m) A U.
  Hypothesis ih_conv : forall Γ A B m s i,
    A <: B ->
    Γ ⊢ m : A : s -> P Γ m A s ->
    [Γ] ⊢ B : s @ i : U -> P [Γ] B (s @ i) U ->
    P Γ m B s.

  Fixpoint clc_type_ind_nested
    Γ m A s (pf : Γ ⊢ m : A : s) : P Γ m A s.
  Proof.
    case pf; intros.
    apply: ih_sort; eauto.
    apply: ih_pi; eauto.
    apply: ih_var; eauto.
    apply: ih_lam; eauto.
    apply: ih_app; eauto.
    apply: ih_indd; eauto.
    have ih_nested :=
      fix fold Cs (pf : All1 (fun C => A0 :U Γ0 ⊢ C : s0 @ l1 : U) Cs) :
        All1 (fun C => P (A0 :U Γ0) C (s0 @ l1) U) Cs :=
        match pf with
        | All1_nil => All1_nil _
        | All1_cons _ _ hd tl =>
          All1_cons (clc_type_ind_nested _ _ _ _ hd) (fold _ tl)
        end; eauto.
    apply: ih_constr; eauto.
    apply: ih_case; eauto.
    have ih_nested :=
      fix fold n Fs Cs
          (pf : All2i (fun i F C =>
                         constr 0 s0 C ∧
                           let T := mkcase k s' I Q (Constr i I s0) C in
                           Γ2 ⊢ F : T.2 : T.1) n Fs Cs) :
        All2i (fun i F C =>
                 constr 0 s0 C ∧
                   let T := mkcase k s' I Q (Constr i I s0) C in
                   P Γ2 F T.2 T.1) n Fs Cs :=
        match pf in All2i _ n Fs Cs return
          All2i (fun i F C =>
                   constr 0 s0 C /\
                     let T := mkcase k s' I Q (Constr i I s0) C in
                     P Γ2 F T.2 T.1) n Fs Cs
        with
        | All2i_nil _ => All2i_nil _ _
        | All2i_cons _ _ _ _ _ (conj h1 h2) tl =>
          All2i_cons (conj h1 (clc_type_ind_nested _ _ _ _ h2)) (fold _ _ _ tl)
        end; eauto.
    apply: ih_fix; eauto.
    apply: ih_conv; eauto.
  Qed.
End clc_type_ind_nested.

Lemma clc_pi_max Γ A B s r t l1 l2 :
  Γ |> U ->
  Γ ⊢ A : s @ l1 : U ->
  [A :{s} Γ] ⊢ B : r @ l2 : U ->
  Γ ⊢ Pi A B s r t : t @ (maxn l1 l2) : U.
Proof.
  move=>k tyA tyB.
  have {}tyA : Γ ⊢ A : s @ (maxn l1 l2) : U.
  apply: clc_conv.
  apply: sub_sort.
  apply: leq_maxl.
  eauto.
  constructor.
  apply: re_pure.
  have {}tyB : [A :{s} Γ] ⊢ B : r @ (maxn l1 l2) : U.
  apply: clc_conv.
  apply: sub_sort.
  apply: leq_maxr.
  eauto.
  constructor.
  apply: re_pure.
  constructor; eauto.
Qed.

(* Well-formed contexts. *)
Inductive ok : context term -> Prop :=
| nil_ok :
  ok nil
| ty_ok Γ A s l :
  ok Γ ->
  [Γ] ⊢ A : s @ l : U ->
  ok (A :{s} Γ)
| n_ok Γ :
  ok Γ ->
  ok (_: Γ).

Lemma re_ok Γ : ok Γ -> ok [Γ].
Proof with eauto using ok.
  elim=>{Γ}...
  move=>Γ A [|] l wf1 wf2 ty//=.
  apply: ty_ok... rewrite<-re_invo; eauto.
  apply: n_ok...
Qed.
