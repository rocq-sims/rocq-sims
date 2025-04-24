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
From OptSim Require Import Utils LTS.

Import CoindNotations.

Section WithLTS.

Context {lts : LTS}.
Notation Observable := lts.(Observable).
Notation St := lts.(St).
Notation trans := lts.(trans).
Notation epsilon := lts.(epsilon).
Notation Robs := lts.(Robs).
Notation ub_state := lts.(ub_state).
Notation label := (@label Observable).

Program Definition divergesF : mon (St -> Prop) :=
{| body R st :=
  exists st', trans tau st st' /\ R st'
|}.
Next Obligation.
  eauto.
Qed.

Definition diverges := gfp divergesF.

#[export] Instance : Proper (St.(Eq) ==> impl) diverges.
Proof.
  cbn. red. coinduction R CH. intros.
  apply (gfp_fp divergesF) in H0. destruct H0 as (? & ? & ?).
  rewrite H in H0. exists x0. eauto.
Qed.

Variant DTauAnswer (R Rind : relation St) s' t : Prop :=
| dtau_match t' (TR : trans tau t t') (DIV : R s' t')
| dtau_div (DIV : Rind s' t)
.
Hint Resolve dtau_match 2 : optsim.
Hint Resolve dtau_div 3 : optsim.

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
  Proper (Eq St ==> Eq St ==> impl) R ->
  Proper (Eq St ==> Eq St ==> impl) (divpresF R).
Proof.
  intro. cbn. intros.
  revert y y0 H0 H1. induction H2. intros. constructor. intros ??.
  rewrite <- H1 in H3.
  apply H0 in H3 as [].
  - rewrite H2 in TR. esim.
  - right. now eapply DIV.
Qed.

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

Definition divpres := gfp divpresF.

Axiom diverges_lem : forall s, diverges s \/ nodiv s.

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

End WithLTS.

Hint Resolve dtau_match 2 : optsim.
Hint Resolve dtau_div 3 : optsim.
Hint Unfold divpresIndF : optsim.
Hint Constructors divpresInd : optsim.
Hint Resolve unfold_divpresF : optsim.
