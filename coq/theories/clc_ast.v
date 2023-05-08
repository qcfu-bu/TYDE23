From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS clc_context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
(* core *)
| Var    (x : var)
| Sort   (s : sort) (l : nat)
| Pi     (A : term) (B : {bind term}) (s r t : sort)
| Lam    (A : term) (m : {bind term}) (s t : sort)
| App    (m n : term)
| Ind    (A : term) (Cs : list {bind term}) (s : sort)
| Constr (i : nat) (m : term) (s : sort)
| Case   (m Q : term) (Fs : list term)
| Fix    (k : nat) (A : term) (m : {bind term})
| Ptr    (l : nat).

Notation "s @ l" := (Sort s l) (at level 30).

#[global] Instance Ids_term : Ids term. derive. Defined.
#[global] Instance Rename_term : Rename term. derive. Defined.
#[global] Instance Subst_term : Subst term. derive. Defined.
#[global] Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive All1 (P : term -> Prop) : list term -> Prop :=
| All1_nil : All1 P nil
| All1_cons m ls : P m -> All1 P ls -> All1 P (m :: ls).

Section term_ind_nested.
  Variable P : term -> Prop.
  Hypothesis ih_var : forall x, P (Var x).
  Hypothesis ih_sort : forall s l, P (Sort s l).
  Hypothesis ih_pi : forall A B s r t, P A -> P B -> P (Pi A B s r t).
  Hypothesis ih_lam : forall A m s t, P A -> P m -> P (Lam A m s t).
  Hypothesis ih_app : forall m n, P m -> P n -> P (App m n).
  Hypothesis ih_ind : forall A Cs s, P A -> All1 P Cs -> P (Ind A Cs s).
  Hypothesis ih_constr : forall i m s, P m -> P (Constr i m s).
  Hypothesis ih_case :
    forall m Q Fs, P m -> P Q -> All1 P Fs -> P (Case m Q Fs).
  Hypothesis ih_fix : forall k A m, P A -> P m -> P (Fix k A m).
  Hypothesis ih_ptr : forall l, P (Ptr l).

  Fixpoint term_ind_nested m : P m.
  Proof.
    have ih_nested :=
      fix fold xs : All1 P xs :=
        match xs with
        | nil => All1_nil _
        | x :: xs => All1_cons (term_ind_nested x) (fold xs)
        end.
    case m; move=>*.
    exact: ih_var.
    exact: ih_sort.
    exact: ih_pi.
    exact: ih_lam.
    exact: ih_app.
    exact: ih_ind.
    exact: ih_constr.
    exact: ih_case.
    exact: ih_fix.
    exact: ih_ptr.
  Qed.
End term_ind_nested.

Fixpoint spine (h : term) (ls : list term) : term :=
  match ls with
  | nil => h
  | m :: ls => spine (App h m) ls
  end.

Inductive iget : nat -> list term -> term -> Prop :=
| iget_O m ls :
  iget 0 (m :: ls) m
| iget_S n m m' ls :
  iget n ls m ->
  iget (S n) (m' :: ls) m.

Inductive One2 R : list term -> list term -> Prop :=
| One2_hd m m' ls :
  R m m' ->
  One2 R (m :: ls) (m' :: ls)
| One2_tl m ls ls' :
  One2 R ls ls' ->
  One2 R (m :: ls) (m :: ls').

Reserved Notation "m ~> n" (at level 30).
Inductive step : term -> term -> Prop :=
| step_beta A m n s t :
  (App (Lam A m s t) n) ~> m.[n/]
| step_lamL A A' m s t :
  A ~> A' ->
  Lam A m s t ~> Lam A' m s t
| step_lamR A m m' s t :
  m ~> m' ->
  Lam A m s t ~> Lam A m' s t
| step_piL A A' B s r t :
  A ~> A' ->
  Pi A B s r t ~> Pi A' B s r t
| step_piR A B B' s r t :
  B ~> B' ->
  Pi A B s r t ~> Pi A B' s r t
| step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
| step_indA A A' Cs s :
  A ~> A' ->
  Ind A Cs s ~> Ind A' Cs s
| step_indCs A Cs Cs' s :
  One2 step Cs Cs' ->
  Ind A Cs s ~> Ind A Cs' s
| step_constr i m m' s :
  m ~> m' ->
  Constr i m s ~> Constr i m' s
| step_caseM m m' Q Fs :
  m ~> m' ->
  Case m Q Fs ~> Case m' Q Fs
| step_caseQ m Q Q' Fs :
  Q ~> Q' ->
  Case m Q Fs ~> Case m Q' Fs
| step_caseFs m Q Fs Fs' :
  One2 step Fs Fs' ->
  Case m Q Fs ~> Case m Q Fs'
| step_iota1 i m ms Q Fs F s :
  iget i Fs F ->
  Case (spine (Constr i m s) ms) Q Fs ~> spine F ms
| step_fixL k A A' m :
  A ~> A' ->
  Fix k A m ~> Fix k A' m
| step_fixR k A m m' :
  m ~> m' ->
  Fix k A m ~> Fix k A m'
| step_iota2 i k A m n ms ns s :
  size ms = k ->
  spine (Fix k A m) (rcons ms (spine (Constr i n s) ns)) ~>
  spine m.[Fix k A m/] (rcons ms (spine (Constr i n s) ns))
where "m ~> n" := (step m n).

Notation red := (star step).
Notation "m ~>* n" := (red m n) (at level 30).
Notation "m === n" := (conv step m n) (at level 50).

Section step_ind_nested.
  Variable P : term -> term -> Prop.
  Hypothesis ih_beta :
    forall A m n s t, P (App (Lam A m s t) n) m.[n/].
  Hypothesis ih_lamL :
    forall A A' m s t, A ~> A' -> P A A' -> P (Lam A m s t) (Lam A' m s t).
  Hypothesis ih_lamR :
    forall A m m' s t, m ~> m' -> P m m' -> P (Lam A m s t) (Lam A m' s t).
  Hypothesis ih_piL :
    forall A A' B s r t, A ~> A' -> P A A' -> P (Pi A B s r t) (Pi A' B s r t).
  Hypothesis ih_piR :
    forall A B B' s r t, B ~> B' -> P B B' -> P (Pi A B s r t) (Pi A B' s r t).
  Hypothesis ih_appL :
    forall m m' n, m ~> m' -> P m m' -> P (App m n) (App m' n).
  Hypothesis ih_appR :
    forall m n n', n ~> n' -> P n n' -> P (App m n) (App m n').
  Hypothesis ih_indA :
    forall A A' Cs s, A ~> A' -> P A A' -> P (Ind A Cs s) (Ind A' Cs s).
  Hypothesis ih_indCs :
    forall A Cs Cs' s, One2 step Cs Cs' -> One2 P Cs Cs' -> P (Ind A Cs s) (Ind A Cs' s).
  Hypothesis ih_constr :
    forall i m m' s, m ~> m' -> P m m' -> P (Constr i m s) (Constr i m' s).
  Hypothesis ih_caseM :
    forall m m' Q Fs, m ~> m' -> P m m' -> P (Case m Q Fs) (Case m' Q Fs).
  Hypothesis ih_caseQ :
    forall m Q Q' Fs, Q ~> Q' -> P Q Q' -> P (Case m Q Fs) (Case m Q' Fs).
  Hypothesis ih_caseFs :
    forall m Q Fs Fs', One2 step Fs Fs' -> One2 P Fs Fs' -> P (Case m Q Fs) (Case m Q Fs').
  Hypothesis ih_iota1 :
    forall i m ms Q Fs F s, iget i Fs F -> P (Case (spine (Constr i m s) ms) Q Fs) (spine F ms).
  Hypothesis ih_fixL :
    forall k A A' m, A ~> A' -> P A A' -> P (Fix k A m) (Fix k A' m).
  Hypothesis ih_fixR :
    forall k A m m', m ~> m' -> P m m' -> P (Fix k A m) (Fix k A m').
  Hypothesis ih_iota2 :
    forall i k A m n ms ns s,
      size ms = k ->
      P (spine (Fix k A m) (rcons ms (spine (Constr i n s) ns)))
        (spine m.[Fix k A m/] (rcons ms (spine (Constr i n s) ns))).

  Fixpoint step_ind_nested m m' (st : m ~> m') : P m m'.
  Proof.
    have ih_nested :=
      fix fold ls1 ls2 (p : One2 step ls1 ls2) : One2 P ls1 ls2 :=
        match p with
        | One2_hd _ _ _ hd => One2_hd _ (step_ind_nested _ _ hd)
        | One2_tl _ _ _ tl => One2_tl _ (fold _ _ tl)
        end.
    case st; move=>*.
    apply: ih_beta.
    apply: ih_lamL; eauto.
    apply: ih_lamR; eauto.
    apply: ih_piL; eauto.
    apply: ih_piR; eauto.
    apply: ih_appL; eauto.
    apply: ih_appR; eauto.
    apply: ih_indA; eauto.
    apply: ih_indCs; eauto.
    apply: ih_constr; eauto.
    apply: ih_caseM; eauto.
    apply: ih_caseQ; eauto.
    apply: ih_caseFs; eauto.
    apply: ih_iota1; eauto.
    apply: ih_fixL; eauto.
    apply: ih_fixR; eauto.
    apply: ih_iota2; eauto.
  Qed.
End step_ind_nested.

Lemma All1_append P ms ms' :
  All1 P ms -> All1 P ms' -> All1 P (ms ++ ms').
Proof with eauto using All1.
  move=>pms. elim: pms ms'=>//={ms}...
Qed.

Lemma All1_rcons P ms m :
  All1 P ms -> P m -> All1 P (rcons ms m).
Proof with eauto using All1.
  move=>pms pm.
  rewrite<-cats1.
  apply: All1_append...
Qed.

Lemma All1_rev P ms : All1 P ms -> All1 P (rev ms).
Proof with eauto using All1.
  elim=>//={ms}...
  move=>m ms pm hd tl.
  replace (m :: ms) with ([:: m] ++ ms) by eauto.
  rewrite rev_cat.
  apply: All1_append...
Qed.
