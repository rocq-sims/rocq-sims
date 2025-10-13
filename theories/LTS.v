(* SPDX-FileCopyrightText: 2025 rocq-sims authors *)
(* SPDX-License-Identifier: LGPL-3.0-or-later *)

From Coq Require Import Morphisms.
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
From Coinduction Require Import all.
From Sims Require Import Utils.

Import CoindNotations.

Variant label {S : Type} := obs (s : S) | tau.

Record LTS := {
  Observable : Type;
  St : EqType;
  trans : @label Observable -> srel St St;
  Robs : Observable -> Observable -> Prop; (* TODO remove *)
}.

Arguments trans {lts} : rename.
Arguments Robs {lts} : rename.

Section LTS.

Context {lts : LTS}.
Context (delay : SimOpt.delay_opt).

Definition is_obs (l : @label lts.(Observable)) := if l then true else false.
Definition is_tau (l : @label lts.(Observable)) := if l then false else true.

Definition is_tau_state st :=
  forall l st', lts.(trans) l st st' -> is_tau l = true.

#[export] Instance is_tau_state_Eq : Proper (lts.(St).(Eq) ==> impl) is_tau_state.
Proof.
  cbn. red. intros. rewrite <- H in H1. now apply H0 in H1.
Qed.

Lemma is_tau_state_obs : forall o st st',
  is_tau_state st ->
  trans (obs o) st st' ->
  False.
Proof.
  intros. now apply H in H0.
Qed.

Definition is_obs_state st :=
  forall l st', lts.(trans) l st st' -> is_obs l = true.

#[export] Instance is_obs_state_Eq : Proper (lts.(St).(Eq) ==> impl) is_obs_state.
Proof.
  cbn. red. intros. rewrite <- H in H1. now apply H0 in H1.
Qed.

Lemma is_obs_state_tau : forall st st',
  is_obs_state st ->
  trans tau st st' ->
  False.
Proof.
  intros. now apply H in H0.
Qed.

(* Stuck and non-stuck LTSs *)

Variant extrans (st : lts.(St)) : Prop :=
  trans_intro l st' : trans l st st' -> extrans st.
Hint Constructors extrans : optsim.

#[export] Instance : Proper (lts.(St).(Eq) ==> flip impl) extrans.
Proof.
  cbn. intros ??? []. rewrite <- H in H0. eauto with optsim.
Qed.

Definition is_stuck (st : lts.(St)) : Prop :=
  ~ extrans st.

#[export] Instance : Proper (lts.(St).(Eq) ==> impl) is_stuck.
Proof.
  cbn. unfold is_stuck. intros. now setoid_rewrite <- H.
Qed.

#[export] Instance : Proper (lts.(St).(Eq) ==> iff) is_stuck.
Proof.
  intros. apply proper_sym_impl_iff; typeclasses eauto.
Qed.

Definition can_be_stuck s :=
  is_stuck s \/ (delay = SimOpt.delay /\ exists s', (trans tau)^* s s' /\ is_stuck s').
Hint Unfold can_be_stuck : optsim.

#[export] Instance : Proper (lts.(St).(Eq) ==> impl) can_be_stuck.
Proof.
  cbn. intros. destruct H0 as [ | (? & ? & ? & ?)].
  - rewrite H in H0. now left.
  - rewrite H in H1. right; eauto.
Qed.

Lemma is_stuck_can_be_stuck : forall s, is_stuck s -> can_be_stuck s.
Proof.
  intros. now left.
Qed.

Lemma can_be_stuck_taustar : forall (Hdelay : delay = SimOpt.delay) s s',
  can_be_stuck s' ->
  (trans tau)^* s s' ->
  can_be_stuck s.
Proof.
  intros. right. destruct H as [| (? & ? & ? & ?)].
  - eauto.
  - assert ((trans tau)^* s x). { rewrite <- str_trans. esplit; eauto. }
    eauto.
Qed.

Lemma trans_add_delay : forall (l : @label lts.(Observable)),
  trans l ≦ (trans tau)^* ⋅ trans l.
Proof.
  intros. esplit; eauto. now rewrite <- str_refl.
Qed.

(* Posibly delayed transition *)

Definition dtrans l st st' :=
  match delay with
  | SimOpt.nodelay => lts.(trans) l st st'
  | SimOpt.delay => ((trans tau)^* ⋅ trans l) st st'
  end.

#[global] Instance dtrans_Eq : forall l,
  Proper (lts.(St).(Eq) ==> lts.(St).(Eq) ==> impl) (dtrans l).
Proof.
  cbn. unfold dtrans. intros. destruct delay; now rewrite <- H, <- H0.
Qed.

Lemma trans_dtrans : forall l st st',
  trans l st st' ->
  dtrans l st st'.
Proof.
  intros. red. destruct delay; auto.
  now rewrite <- str_refl, dot1x.
Qed.

Lemma delay_trans_dtrans : forall (Hdelay : delay = SimOpt.delay) l st st',
  ((trans tau)^* ⋅ trans l) st st' ->
  dtrans l st st'.
Proof.
  intros. red. now rewrite Hdelay.
Qed.

Lemma dtrans_trans : forall l st st',
  dtrans l st st' ->
  ((trans tau)^* ⋅ trans l) st st'.
Proof.
  intros. red in H. destruct delay; auto.
  now rewrite <- str_refl, dot1x.
Qed.

Lemma dtrans_case : forall l st st',
  dtrans l st st' ->
  trans l st st' \/
  (delay = SimOpt.delay /\ ((trans tau)^+ ⋅ trans l) st st').
Proof.
  intros. red in H. destruct delay.
  - rewrite str_itr, dotplsx, dot1x in H. destruct H.
    + now left.
    + now right.
  - now left.
Qed.

Lemma dtrans_tauplus : forall s s',
  dtrans tau s s' ->
  (lts.(trans) tau)^+ s s'.
Proof.
  intros. apply dtrans_trans in H. now rewrite <- itr_str_r in H.
Qed.


(* Epsilon *)

Definition epsilon s s' := forall l t, lts.(trans) l s' t -> trans l s t.

#[export] Instance epsilon_Eq : Proper (lts.(St).(Eq) ==> lts.(St).(Eq) ==> impl) epsilon.
Proof.
  cbn. red. intros.
  rewrite <- H. rewrite <- H0 in H2. now apply H1.
Qed.

Lemma epsilon_plus : forall l s s' t,
  epsilon s s' ->
  (trans l)^+ s' t ->
  (trans l)^+ s t.
Proof.
  intros. rewrite itr_str_l in H0 |- *.
  destruct H0. apply H in H0.
  esplit; eauto.
Qed.

Lemma epsilon_dtrans : forall l s s' t,
  epsilon s s' ->
  dtrans l s' t ->
  dtrans l s t.
Proof.
  intros. apply dtrans_case in H0 as [].
  - apply H in H0. now apply trans_dtrans.
  - red. destruct H0 as [-> ?].
    rewrite <- str_itr'.
    rewrite itr_str_l, <- dotA in H0 |- *. destruct H0.
    esplit; eauto.
Qed.

Lemma epsilon_is_stuck : forall s s',
  epsilon s s' ->
  is_stuck s ->
  is_stuck s'.
Proof.
  intros ?????. apply H0. destruct H1.
  apply H in H1. econstructor; eauto.
Qed.

Lemma epsilon_can_be_stuck : forall s s',
  epsilon s s' ->
  extrans s' ->
  can_be_stuck s' ->
  can_be_stuck s.
Proof.
  intros ?????. red. destruct H1 as [| (-> & ? & ? & ?)].
  - now apply H1 in H0.
  - right. split; auto.
    rewrite str_itr in H1. destruct H1.
    + cbn in H1. rewrite H1 in H0. now apply H2 in H0.
    + eapply epsilon_plus in H1; eauto.
      exists x. split; auto. now rewrite <- str_itr'.
Qed.


(* From P st : all the states reachable from st verify property P. *)

Program Definition fromF P : mon (lts.(St) -> Prop) :=
  {| body := fun P' st => P st /\ forall l st', trans l st st' -> P' st' |}.
Next Obligation.
  eauto.
Qed.

#[export] Instance fromF_eq : forall P P',
  Proper (lts.(St).(Eq) ==> impl) P ->
  Proper (lts.(St).(Eq) ==> impl) (fromF P P').
Proof.
  intros. cbn. intros. destruct H1. split.
  now rewrite <- H0.
  intros. eapply H2. rewrite H0. apply H3.
Qed.

Definition From P := gfp (fromF P).

#[export] Instance Chain_fromF_eq : forall P (C : Chain (fromF P)),
  Proper (lts.(St).(Eq) ==> impl) P ->
  Proper (lts.(St).(Eq) ==> impl) (`C).
Proof.
  intros ???. apply tower; clear C.
  { intros ????????. eapply H0; eauto. }
  intros C **. cbn. intros. rewrite <- H1. split; auto.
  now destruct H2.
  intros. eapply H2. rewrite H1. apply H3.
Qed.

#[export] Instance From_eq : forall P,
  Proper (lts.(St).(Eq) ==> impl) P ->
  Proper (lts.(St).(Eq) ==> impl) (From P).
Proof.
  intros. typeclasses eauto.
Qed.

Lemma forall_from : forall (P : lts.(St) -> Prop),
  (forall st, P st) -> forall st, From P st.
Proof.
  intros ??. red. coinduction R CH. intros.
  split; auto.
Qed.

Lemma from_id : forall [P : lts.(St) -> Prop] [st],
  From P st ->
  P st.
Proof.
  intros. now apply (gfp_fp (fromF _)) in H as [].
Qed.

Lemma from_trans : forall (P : lts.(St) -> Prop) l st st',
  From P st ->
  trans l st st' ->
  From P st'.
Proof.
  intros. apply (gfp_fp (fromF _)) in H as []. eapply H1; eauto.
Qed.
Hint Resolve from_trans : optsim.

Lemma from_taustar : forall (P : lts.(St) -> Prop) (P_Eq: Proper (lts.(St).(Eq) ==> impl) P) st st',
  From P st ->
  (trans tau)^* st st' ->
  From P st'.
Proof.
  intros.
  eapply srel_str_ind_r with (P := From P); eauto.
  typeclasses eauto.
  clear st st' H H0.
  intros. apply (gfp_fp (fromF P)) in H0 as [].
  apply H1 in H. apply H.
Qed.


End LTS.

Lemma can_be_stuck_delay : forall {lts} (s : lts.(St)),
  can_be_stuck SimOpt.delay s ->
  exists s', (trans tau)^* s s' /\ is_stuck s'.
Proof.
  intros. destruct H.
  - exists s. split; auto. now rewrite <- str_refl.
  - apply H.
Qed.

Lemma tauplus_dtrans {lts} : forall s s',
  (lts.(trans) tau)^+ s s' -> dtrans SimOpt.delay tau s s'.
Proof.
  intros. red. now rewrite <- itr_str_r.
Qed.

Hint Resolve is_tau_state_obs : optsim.
Hint Resolve is_obs_state_tau : optsim.

Hint Constructors extrans : optsim.
Hint Unfold can_be_stuck : optsim.

Hint Resolve trans_dtrans : optsim.
(*Hint Resolve delay_trans_dtrans : optsim.*)
Hint Resolve dtrans_trans : optsim.

Hint Resolve from_trans : optsim.
