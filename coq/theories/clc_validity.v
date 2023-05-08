From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_arity_spine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma merge_context_ok_inv Γ Γ1 Γ2 :
  Γ1 ∘ Γ2 => Γ -> ok Γ -> ok Γ1 /\ ok Γ2.
Proof with eauto using ok.
  elim=>{Γ1 Γ2 Γ}...
  move=>Γ1 Γ2 Γ m mrg ih o. inv o.
  { move:(merge_re_re mrg)=>[_[e1 e2]].
    move:(ih H1)=>{ih H1}[o1 o2].
    split.
    apply: ty_ok...
    rewrite e1...
    apply: ty_ok...
    rewrite e2... }
  move=>Γ1 Γ2 Γ m mrg ih o. inv o.
  { move:(merge_re_re mrg)=>[_[e1 e2]].
    move:(ih H1)=>{ih H1}[o1 o2].
    split.
    apply: ty_ok...
    rewrite e1...
    apply: n_ok... }
  move=>Γ1 Γ2 Γ m mrg ih o. inv o.
  { move:(merge_re_re mrg)=>[_[e1 e2]].
    move:(ih H1)=>{ih H1}[o1 o2].
    split.
    apply: n_ok...
    apply: ty_ok...
    rewrite e2... }
  move=>Γ1 Γ2 Γ mrg ih o. inv o.
  { move:(merge_re_re mrg)=>[_[e1 e2]].
    move:(ih H0)=>{ih H0}[o1 o2].
    split... }
Qed.

Theorem validity Γ m A s :
  ok Γ -> Γ ⊢ m : A : s -> exists l, [Γ] ⊢ A : s @ l : U.
Proof with eauto using clc_type, re_pure, merge_re_id.
  move=>wf tp. move: Γ m A s tp wf.
  apply: clc_type_ind_nested.
  move=>Γ s l k o. exists l.+2...
  move=>Γ A B s r t i k tyA ihA tyB ihB o. exists i.+1...
  move=>Γ x A s hs o. move:(has_ok o hs)=>[l tyA]. exists l...
  move=>Γ A B m s r t i k tyP ihP tym ihm o. exists i...
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn o.
  { move:(merge_context_ok_inv mrg o)=>[o1 o2].
    move:(merge_re_re mrg)=>[e1[e2 e3]].
    move:o1=>/ihm{ihm}[l1/pi_inv[l2[tyA[_[_ tyB]]]]].
    destruct s; exists l2.
    have {}mrg : [Γ1] ∘ Γ2 => [Γ].
      replace Γ2 with [Γ2].
      rewrite e2 e3...
      rewrite<-pure_re...
    by apply: (substitution tyB k mrg tyn).
    move:(substitutionN tyB tyn).
    by rewrite e2. }
  move=>Γ A Cs s l1 l2 k ar cCs tyA _ tyCs ihCs wf.
  { exists l2. rewrite<-pure_re; eauto. }
  move=>Γ A s i C Cs//=k ig tyI ihI wf.
  { have[l1[l2[_[_[ar[cCs[tyA tyCs]]]]]]]:=ind_inv tyI.
    exists l1.
    have tyC:=iget_All1 ig tyCs.
    replace (s @ l1) with (s @ l1).[Ind A Cs s/] by autosubst.
    apply: substitution...
    rewrite<-pure_re...
    apply: merge_pure... }
  move=>Γ1 Γ2 Γ A Q s s' l k Fs Cs m ms//=leq ar key mrg tym ihm tyQ ihQ tyFs ihFs wf.
  { have[wf1 wf2]:=merge_context_ok_inv mrg wf.
    have[e0[<- e2]]:=merge_re_re mrg.
    have{ihm}[l0 tysp]:=ihm wf1.
    have k1 : [Γ1] |> U by apply re_pure.
    have[sp _]:=ind_spine_inv k1 ar tysp.
    have tyI:=ind_spine k1 tysp.
    have {}sp:=rearity_spine s' sp ar leq k1 tyI.
    rewrite<-e0 in tyQ.
    have mrg1:=merge_re_id Γ1.
    have tySp:=app_arity_spine tyQ sp mrg1.
    exists l. destruct k=>//=; simpl in tySp.
    replace (s' @ l) with (s' @ l).[m/] by autosubst.
    apply: clc_app...
    rewrite<-pure_re...
    inv leq... }
  move=>Γ k0 A m l k tyA ihA tym ihm wf. exists l. rewrite<-pure_re...
  move=>Γ A B m s i sb tym ihm tyB ihB o. exists i...
Qed.
