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
From OptSim Require Import Utils.

Variant label {S : Type} := obs (s : S) | tau.

Record LTS := {
  Observable : Type;
  St : EqType;
  trans : @label Observable -> srel St St;
  (*epsilon : srel St St; (* TODO remove *)*)
  Robs : Observable -> Observable -> Prop; (* TODO remove *)
  ub_state : St -> Prop; (* TODO remove *)
}.

Arguments trans {lts} : rename.
(*Arguments epsilon {lts} : rename.*)
Arguments Robs {lts} : rename.
Arguments ub_state {lts} : rename.

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

#[global] Instance :
  Proper (weq ==> eq ==> eq ==> iff) (hrel_of (n := lts.(St)) (m := lts.(St))).
Proof.
  cbn. intros. subst. apply H.
Qed.

#[global] Instance : Proper (leq ==> eq ==> eq ==> impl) (hrel_of (n := lts.(St)) (m := lts.(St))).
Proof.
  cbn. intros. subst. now apply H.
Qed.

#[global] Instance :
  Proper (weq ==> eq ==> eq ==> iff) (hrel_of (n := lts.(St)) (m := lts.(St))).
Proof.
  cbn. intros. subst. apply H.
Qed.

#[global] Instance : Proper (leq ==> eq ==> eq ==> impl) (hrel_of (n := lts.(St)) (m := lts.(St))).
Proof.
  cbn. intros. subst. now apply H.
Qed.

Definition is_obs (l : @label lts.(Observable)) := if l then true else false.
Definition is_tau (l : @label lts.(Observable)) := if l then false else true.

Definition is_tau_state st :=
  forall l st', lts.(trans) l st st' -> is_tau l = true.

Definition is_obs_state st :=
  forall l st', lts.(trans) l st st' -> is_obs l = true.

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

End LTS.

Hint Constructors extrans : optsim.
Hint Unfold can_be_stuck : optsim.
