(* SPDX-FileCopyrightText: 2025 rocq-sims authors *)
(* SPDX-License-Identifier: LGPL-3.0-or-later *)

From Coq Require Import Program.Equality.
From Coinduction Require Import all.
From RelationAlgebra Require Import
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation
     monoid.
From Sims Require Import Utils LTS.

Import CoindNotations.

Section WithLTS.

Context {lts : LTS}.
Notation Observable := lts.(Observable).
Notation St := lts.(St).
Notation trans := lts.(trans).
Notation Robs := lts.(Robs).
Notation label := (@label Observable).

Program Definition divergesF : mon (St -> Prop) :=
{| body R st :=
  exists st', trans tau st st' /\ R st'
|}.
Next Obligation.
  eauto.
Qed.

Definition diverges := gfp divergesF.

#[export] Instance :
  forall R,
  Proper (St.(Eq) ==> impl) (divergesF R).
Proof.
  intros. cbn. intros. destruct H0 as (? & ? & ?).
  setoid_rewrite <- H. eauto.
Qed.

#[export] Instance : Proper (St.(Eq) ==> impl) diverges.
Proof.
  cbn. red. intros. apply (gfp_fp divergesF).
  apply (gfp_fp divergesF) in H0. now rewrite H in H0.
Qed.

Lemma divergesF_taustar : forall (R : Chain divergesF) s s',
  (trans tau)^* s s' ->
  `R s' ->
  `R s.
Proof.
  intro. apply tower. {
    intros ????????. eapply H; eauto.
  }
  intros. rewrite str_itr in H0. destruct H0.
  - cbn in H0. now rewrite H0.
  - rewrite itr_str_l in H0. destruct H0.
    exists x0. split; auto. eapply H. apply H2.
    now apply (b_chain x).
Qed.

Lemma divergesF_tauplus : forall (R : Chain divergesF) s s',
  (trans tau)^+ s s' ->
  `R s' ->
  divergesF `R s.
Proof.
  intros. rewrite itr_str_l in H. destruct H.
  exists x. split; auto. eapply divergesF_taustar; eauto.
Qed.

Lemma diverges_tauplus : forall s s',
  (trans tau)^+ s s' ->
  diverges s' ->
  diverges s.
Proof.
  unfold diverges. apply gfp_prop.
  intros. apply (b_chain x). eapply divergesF_tauplus; eauto.
Qed.

Lemma diverges_obs_state :
  forall st, is_obs_state st -> diverges st -> False.
Proof.
  intros.
  apply (gfp_fp divergesF) in H0 as (? & ? & _).
  now apply H in H0.
Qed.


(* Non-divergence *)

Inductive nodiv s : Prop :=
| nodiv_tau : (forall s', trans tau s s' -> nodiv s') -> nodiv s
.

Lemma diverges_nodiv : forall s,
  nodiv s ->
  diverges s ->
  False.
Proof.
  intros. induction H.
  apply (gfp_fp divergesF) in H0 as (? & ? & ?).
  apply H1 in H0 as [].
  apply H2.
Qed.

Lemma diverges_impl_nodiv : forall (s t : St),
  nodiv s \/ diverges t ->
  (diverges s -> diverges t).
Proof.
  intros. destruct H.
  - now apply diverges_nodiv in H; auto.
  - apply H.
Qed.


(* Divergence preservation *)

Variant DTauAnswer (R Rind : relation St) s' t : Prop :=
| dtau_match t' (TR : trans tau t t') (DIV : R s' t')
| dtau_div (DIV : Rind s' t)
.

Hint Resolve dtau_match | 2 : optsim.
Hint Resolve dtau_div | 3 : optsim.

#[export] Instance DTauAnswer_eq R Rind :
  Proper (Eq St ==> Eq St ==> impl) R ->
  Proper (Eq St ==> Eq St ==> impl) Rind ->
  Proper (Eq St ==> Eq St ==> impl) (DTauAnswer R Rind).
Proof.
  intros. cbn. intros. destruct H3.
  - rewrite H2 in TR. rewrite H1 in DIV. esim.
  - rewrite H1, H2 in DIV. esim.
Qed.

Definition divpresIndF R Rind s t :=
  forall s', trans tau s s' -> DTauAnswer R Rind s' t.
Hint Unfold divpresIndF : optsim.

Section NoElim.
#[local] Unset Elimination Schemes.
Inductive divpresInd R s t : Prop :=
| divpresI : divpresIndF R (divpresInd R) s t -> divpresInd R s t.
End NoElim.
Hint Constructors divpresInd : optsim.

Definition divpresInd_ind :
  forall R P : St -> St -> Prop,
       (forall s t : St,
         (divpresIndF R (fun s t => divpresInd R s t /\ P s t) s t) -> 
        P s t) -> forall t t0 : St, divpresInd R t t0 -> P t t0.
Proof.
  intros until 1. fix F 3. intros. apply H. destruct H0.
  red. intros. apply H0 in H1 as [].
  - eleft; eauto.
  - eright; eauto.
Qed.

Program Definition divpresF : mon (St -> St -> Prop) :=
{| body R s t := divpresInd R s t |}.
Next Obligation.
  induction H0. constructor. intros ??.
  apply H0 in H1 as []. eleft; eauto. eright; eauto. apply DIV.
Qed.

Lemma unfold_divpresF : forall R s t,
 divpresInd R s t ->
 divpresF R s t.
Proof.
  auto.
Qed.
Hint Resolve unfold_divpresF : optsim.

#[export] Instance divpresF_eq R :
  Proper (Eq St ==> Eq St ==> impl) (divpresF R).
Proof.
  intro. cbn. intros.
  revert y y0 H H0. induction H1. intros. constructor. intros ??.
  rewrite <- H0 in H2.
  apply H in H2 as [].
  - rewrite H1 in TR. esim.
  - right. now eapply DIV.
Qed.

#[export] Instance Chain_divpresF_eq (R : Chain divpresF) :
  Proper (Eq St ==> Eq St ==> impl) `R.
Proof.
  apply tower. { intros ???????????. eapply H; eauto. }
  typeclasses eauto.
Qed.

#[export] Instance : forall (R : Chain divergesF),
  Proper (St.(Eq) ==> impl) `R.
Proof.
  intro. apply tower. {
    intros ????????. eapply H; eauto.
  }
  intros. typeclasses eauto.
Qed.

Definition divpres := gfp divpresF.

Lemma divpres_impl : forall s t,
  divpres s t ->
  diverges s -> diverges t.
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp divpresF) in H. induction H. apply (gfp_fp divergesF) in H0 as (? & ? & ?).
  apply H in H0 as [].
  - exists t'. eauto.
  - now apply DIV.
Qed.

Lemma diverges_divpres :
  forall s t, diverges t -> divpres s t.
Proof.
  red. coinduction R CH.
  intros. constructor. intros ??.
  apply (gfp_fp divergesF) in H as (? & ? & ?).
  eleft; eauto.
Qed.

Lemma nodiv_divpres :
  forall s t, nodiv s -> divpres s t.
Proof.
  red. intros. induction H.
  apply (gfp_fp divpresF).
  constructor. red. intros.
  apply H0 in H1.
  apply dtau_div.
  apply (gfp_fp divpresF) in H1. apply H1.
Qed.

Lemma divpresF_tau_r : forall (R : Chain divpresF) s t t',
  `R s t' ->
  (trans tau)^* t t' ->
  `R s t.
Proof.
  intro. apply tower. {
    intros ?????????. eapply H; eauto.
  }
  clear R. intros R **.
  induction H0.
  constructor. intros ??.
  apply H0 in H2 as [].
  - assert ((trans tau)^+ t t'). { rewrite itr_str_r. esplit; eassumption. }
    rewrite itr_str_l in H2. destruct H2. esim.
  - apply dtau_div. now apply DIV.
Qed.

Lemma dtau_plus : forall (R : Chain divpresF) Rind s' t t',
  (trans tau)^+ t t' ->
  `R s' t' ->
  DTauAnswer `R Rind s' t.
Proof.
  intros.
  rewrite itr_str_l in H. destruct H.
  eapply dtau_match. apply H.
  eapply divpresF_tau_r; eauto.
Qed.

End WithLTS.

Module Classical.

From Coq Require Import Logic.Classical.

Lemma nodiv_diverges {lts : LTS} : forall (s : lts.(St)),
  ~nodiv s ->
  diverges s.
Proof.
  red. coinduction R CH. intros.
  assert (~(forall s', trans tau s s' -> nodiv s')). { intro. apply H. now constructor. }
  eapply not_all_ex_not in H0. destruct H0 as [s' ?].
  apply imply_to_and in H0.
  exists s'. intuition.
Qed.

Lemma diverges_lem {lts : LTS} : forall (s : lts.(St)), diverges s \/ nodiv s.
Proof.
  intros.
  pose proof (nodiv_diverges s).
  apply imply_to_or in H.
  destruct H; auto. apply NNPP in H; auto.
Qed.

Lemma trans_case {lts : LTS} :
  forall (s : lts.(St)),
  diverges s \/ can_be_stuck SimOpt.delay s \/ exists o s', ((trans tau)^*⋅(trans (obs o))) s s'.
Proof.
  intros. destruct (diverges_lem s); auto. right.
  induction H. destruct (classic (is_stuck s)).
  - left. now left.
  - apply NNPP in H1. destruct H1. destruct l.
    + right. exists s0, st'. now rewrite <- str_refl, dot1x.
    + apply H0 in H1 as ?. destruct H2 as [| (? & ? & ?)].
      * left. eapply can_be_stuck_taustar in H2; eauto. now rewrite <- str_ext.
      * right. exists x, x0. destruct H2. esplit; eauto.
        rewrite str_unfold_l. right. esplit; eauto.
Qed.

Lemma diverges_lem_extrans {lts : LTS} :
  forall (s : lts.(St)),
  (forall (s s' : lts.(St)), trans tau s s' -> extrans s') ->
  extrans s -> diverges s \/ exists o s', ((trans tau)^*⋅(trans (obs o))) s s'.
Proof.
  intros. destruct (diverges_lem s); auto. right.
  induction H1. destruct H0. destruct l.
  - exists s0, st'. esplit; eauto. now rewrite <- str_refl.
  - apply H2 in H0 as ?; eauto.
    destruct H3 as (o & s' & ?). exists o, s'.
    destruct H3. esplit; eauto. rewrite str_unfold_l. right.
    esplit; eauto.
Qed.

Theorem divpres_equiv {lts : LTS} : forall (s t : lts.(St)),
  divpres s t <->
  (diverges s -> diverges t).
Proof.
  split. { apply divpres_impl. }
  intros.
  destruct (diverges_lem t).
  { now apply diverges_divpres. }
  destruct (diverges_lem s).
  - apply H in H1. now apply diverges_divpres.
  - now apply nodiv_divpres.
Qed.

End Classical.

Hint Resolve dtau_match | 2 : optsim.
Hint Resolve dtau_div | 3 : optsim.
Hint Unfold divpresIndF : optsim.
Hint Constructors divpresInd : optsim.
Hint Resolve unfold_divpresF : optsim.
