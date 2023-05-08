From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS clc_context clc_ast clc_confluence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sub1 : term -> term -> Prop :=
| sub1_refl A : 
  sub1 A A
| sub1_sort s l1 l2 : 
  l1 <= l2 -> 
  sub1 (s @ l1) (s @ l2)
| sub1_pi A B1 B2 s r t : 
  sub1 B1 B2 -> 
  sub1 (Pi A B1 s r t) (Pi A B2 s r t).

CoInductive sub (A B : term) : Prop :=
| SubI A' B' : 
  sub1 A' B' -> A === A' -> B' === B -> sub A B.
Infix "<:" := sub (at level 50, no associativity).

Lemma sub1_sub A B : sub1 A B -> sub A B. move=> /SubI. exact. Qed.
Lemma sub1_conv B A C : sub1 A B -> B === C -> A <: C. move=>/SubI. exact. Qed.
Lemma conv_sub1 B A C : A === B -> sub1 B C -> A <: C. move=>c/SubI. exact. Qed.

Lemma conv_sub A B : A === B -> A <: B.
Proof. move/conv_sub1. apply. exact: sub1_refl. Qed.

Lemma sub_refl A : A <: A.
Proof. apply: sub1_sub. exact: sub1_refl. Qed.
#[global] Hint Resolve sub_refl.

Lemma sub_sort s n m : n <= m -> s @ n <: s @ m.
Proof. move=> leq. exact/sub1_sub/sub1_sort. Qed.

Lemma sub1_trans A B C D :
  sub1 A B -> B === C -> sub1 C D -> A <: D.
Proof with eauto 6 using sub1, sub1_sub, sub1_conv, conv_sub1.
  move=> sb. elim: sb C D => {A B}
    [ A C D 
    | s l1 l2 leq C D conv sb
    | A B1 B2 s r t sb1 ih C D conv sb2]...
  inv sb; try (exfalso; solve_conv)...
    move: conv => /sort_inj [->eq].
    apply: sub_sort. subst.
    exact: leq_trans leq _.
  inv sb2; try (exfalso; solve_conv)...
    move: conv => /pi_inj[conv1 [conv2[->[->->]]]].
    move: (ih _ _ conv2 H) => {ih} sub. inv sub.
    apply: SubI. 
    apply sub1_pi with (s := s0) (r := r0) (t := t0)... 
    exact: conv_pi. 
    exact: conv_pi.
Qed.

Lemma sub_trans B A C :
  A <: B -> B <: C -> A <: C.
Proof.
  move=> [A' B' s1 c1 c2] [B'' C' s2 c3 c4]. move: (conv_trans _ c2 c3) => h.
  case: (sub1_trans s1 h s2) => A0 B0 s3 c5 c6. apply: (SubI s3).
  exact: conv_trans c5. exact: conv_trans c4.
Qed.

Lemma sub_sort_inv s1 s2 l1 l2 :
  s1 @ l1 <: s2 @ l2 -> s1 = s2 /\ l1 <= l2.
Proof.
  move=> [s1' s2' []].
  move=> A c1 c2.
    have{c1 c2}/sort_inj[s l]: s1 @ l1 === s2 @ l2.
      exact: conv_trans c2.
    inv l=> //.
  move=> s l0 l3 leq /sort_inj[->->]/sort_inj[<-<-]=> //.
  move=> *. exfalso; solve_conv.
Qed.

Lemma sub_sort_false1 l1 l2 : ~U @ l1 <: L @ l2.
Proof.
  move=>[s1 s2[]].
  move=>A e1 e2.
    have e : U @ l1 === L @ l2.
      exact: conv_trans e2.
    solve_conv.
  move=>s l3 l4 _/sort_inj[<-_]h. solve_conv.
  move=>A B1 B2 s r t _ e1 e2. solve_conv.
Qed.

Lemma sub_sort_false2 l1 l2 : ~L @ l1 <: U @ l2.
Proof.
  move=>[s1 s2[]].
  move=>A e1 e2.
    have e : L @ l1 === U @ l2.
      exact: conv_trans e2.
    solve_conv.
  move=>s l3 l4 _/sort_inj[<-_]h. solve_conv.
  move=>A B1 B2 s r t _ e1 e2. solve_conv.
Qed.

Lemma sub_pi_inv A1 A2 s1 s2 r1 r2 t1 t2 B1 B2 :
  Pi A1 B1 s1 r1 t1 <: Pi A2 B2 s2 r2 t2 -> 
    A1 === A2 /\ B1 <: B2 /\ s1 = s2 /\ r1 = r2 /\ t1 = t2.
Proof.
  move=> [A' B' []].
  move=> C c1 c2. 
    have{c1 c2}/pi_inj[c1[c2[->[->->]]]]: 
      Pi A1 B1 s1 r1 t1 === Pi A2 B2 s2 r2 t2.
    exact: conv_trans c2.
    firstorder=>//. exact: conv_sub.
  move=> *. exfalso; solve_conv.
  move=> A B0 B3 s r t sb 
    /pi_inj[c1[c2[<-[<-<-]]]]/pi_inj[c3[c4[->[->->]]]]. 
    firstorder.
    exact: conv_trans c3. exact: SubI sb c2 c4.
Qed.

Lemma sub1_subst σ A B : sub1 A B -> sub1 A.[σ] B.[σ].
Proof. move=> s. elim: s σ => /=; eauto using sub1. Qed.

Lemma sub_subst σ A B : A <: B -> A.[σ] <: B.[σ].
Proof. move=> [A' B' /sub1_subst]; eauto using sub, conv_subst. Qed.

Lemma sub_ren A B ξ : A <: B -> A.[ren ξ] <: B.[ren ξ].
Proof. move=> *; by apply: sub_subst. Qed.

Ltac solve_sub :=
  match goal with
  | [ H : _ <: _ |- _ ] =>
    let A := fresh "A" in
    let B := fresh "B" in
    let sb := fresh "sb" in
    let c1 := fresh "c1" in
    let c2 := fresh "c2" in
    destruct H as [A B sb c1 c2]; destruct sb
  end;
  match goal with
  | [ c1 : ?A === ?x, c2 : ?x === ?B |- _ ] =>
    assert (A === B) by
      (eapply conv_trans; try solve [apply c1| apply c2]);
    clear c1 c2;
    solve_conv
  | _ => solve_conv
  end.
