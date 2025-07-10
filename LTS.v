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
From Sims Require Import Utils.

Variant label {S : Type} := obs (s : S) | tau.

Record LTS := {
  Observable : Type;
  St : EqType;
  trans : @label Observable -> srel St St;
  Robs : Observable -> Observable -> Prop; (* TODO remove *)
}.

Arguments trans {lts} : rename.
Arguments Robs {lts} : rename.

(*Section LockLTS.

  Context (lts : LTS).
  Variant LockObservable := | Event (e : lts.(Observable)) | NoEvent.
  Program Definition LockSt := {| type_of := (bool * lts.(St))%type |}.
  Variant locktrans : @label LockObservable -> LockSt -> LockSt -> Prop :=
  | locktrans_ev b o s t : lts.(trans) (obs o) s t -> locktrans (obs (Event o)) (b, s) (true, t)
  | locktrans_noev s : (forall l t, lts.(trans) l s t -> False) -> locktrans (obs NoEvent) (true, s) (true, s)
  .
  Definition lockepsilon : LockSt -> LockSt -> Prop :=
    fun '(b, s) '(b', s') =>
    lts.(epsilon) s s' /\ (
      (b = false /\ b' = false) \/
      (b = true /\ b' = false) \/
      (b = true /\ b' = true /\ forall l s'', lts.(trans) l s s'' -> False)
    ).
  Definition LockRobs : LockObservable -> LockObservable -> Prop. Admitted.
  Definition lock_ub_state : LockSt -> Prop. Admitted.

  Definition lock := {|
    Observable := LockObservable;
    St := LockSt;
    trans := locktrans;
    epsilon := lockepsilon;
    Robs := LockRobs;
    ub_state := lock_ub_state
  |}.

End LockLTS.*)

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

#[export] Instance : Proper (lts.(St).(Eq) ==> flip impl) is_stuck.
Proof.
  cbn. unfold is_stuck. intros. now setoid_rewrite H.
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

End LTS.

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
