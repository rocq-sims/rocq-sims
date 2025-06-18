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
From OptSim Require Import Utils LTS Divergence OptSim.

Import CoindNotations.

Section WithLTS.

Context {lts : LTS}.

Notation Observable := lts.(Observable).
Notation St := lts.(St).
Notation trans := lts.(trans).
(*Notation epsilon := lts.(epsilon).*)
Notation Robs := lts.(Robs).
Notation ub_state := lts.(ub_state).
Notation label := (@label Observable).

Program Definition divsimF lock : mon (St -> St -> Prop) :=
{|
  body := fun R s t => (forall o s', trans (obs o) s s' ->
    exists o' t',
        ((trans tau)^* ⋅ trans (obs o')) t t' /\
      R s' t' /\
      Robs o o') /\
  (forall s', trans tau s s' ->
    exists t', 
      (trans tau)^* t t' /\ R s' t') /\
  (diverges s -> diverges t) /\
  lockpres lock SimOpt.delay s t
|}.
Next Obligation.
  repeat split; intros; auto.
  - apply H0 in H4 as (? & ? & ? & ? & ?). eauto 6.
  - apply H1 in H4 as (? & ? & ?). eauto.
Qed.

#[export] Instance : forall lock R,
  Proper (St.(Eq) ==> St.(Eq) ==> impl) (divsimF lock R).
Proof.
  cbn -[divsimF]. intros. repeat split; intros.
  - rewrite <- H in H2. apply H1 in H2 as (? & ? & ? & ? & ?).
    exists x1, x2. repeat split; auto. now rewrite <- H0.
  - rewrite <- H in H2. apply H1 in H2 as (? & ? & ?).
    exists x1. split; auto. now rewrite <- H0.
  - rewrite <- H in H2. apply H1 in H2. now rewrite <- H0.
  - rewrite <- H, <- H0. apply H1.
Qed.

#[export] Instance : forall lock (R : Chain (divsimF lock)),
  Proper (St.(Eq) ==> St.(Eq) ==> impl) `R.
Proof.
  intro. apply tower. {
    intros ???????????. eapply H; eauto.
  }
  intros. typeclasses eauto.
Qed.

Definition divsim lock := gfp (divsimF lock).

Section WithOpts.

Context (freeze : SimOpt.freeze_opt)
  (lock : SimOpt.lock_opt) (delay : SimOpt.delay_opt).

Lemma divsim_divpres : forall s t,
  divsim lock s t ->
  sim freeze lock delay false s t.
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp (divsimF _)) in H. destruct H as (_ & _ & ? & _).
  destruct (Classical.diverges_lem s).
  apply H in H0. eapply chain_div in H0. apply H0; auto.
  eapply chain_nodiv with (R := R) (t := t) in H0. apply H0; auto.
Qed.

Lemma divsim_sim
  (Hfreeze : freeze = SimOpt.freeze_div)
  (Hdelay : delay = SimOpt.delay) :
  forall b s t, divsim lock s t ->
  sim freeze lock delay b s t.
Proof.
  red. coinduction R CH. intros. destruct b.
  2: { now apply (gfp_bchain R), divsim_divpres. }
  constructor.
  repeat split; intros.
  - apply (gfp_fp (divsimF _)) in H. destruct H as (? & ? & _).
    apply H in H0 as (? & ? & ? & ? & ?).
    eapply ans_obs; esim. now eapply delay_trans_dtrans.
  - apply (gfp_fp (divsimF _)) in H.
    apply H in H0 as (? & ? & ?).
    rewrite str_itr in H0. destruct H0.
    + cbn in H0. apply tau_div; auto.
      * apply CH. rewrite H0. apply H1.
      * apply CH. rewrite H0. apply H1.
    + eapply tau_delay; eauto.
  - apply (gfp_fp (divsimF _)) in H. rewrite Hdelay. apply H.
Qed.

Lemma sim_divsim
  (Hfreeze : freeze = SimOpt.freeze_div)
  (Hdelay : delay = SimOpt.delay)
  (OBS : Transitive Robs) :
  forall s t, sim freeze lock delay true s t ->
  divsim lock s t.
Proof.
  red. coinduction R CH. intros. cbn -[dot str]. repeat split; intros.
  - apply sim_fp in H. apply H in H0 as []; auto.
    apply itr_sim in SIM; auto. exists o', t'. split; esim.
  - apply sim_fp in H. apply H in H0 as []; auto.
    + exists t'. split. { now rewrite <- str_ext. }
      now apply CH.
    + now rewrite Hfreeze in H0.
    + exists t. split. { now rewrite <- str_refl. }
      now apply CH.
    + exists t'. split. { now rewrite <- str_itr'. }
      now apply CH.
  - apply sim_f_t in H; auto. revert s t H H0. clear R CH. red. coinduction R CH. intros.
    cbn. apply sim_fp in H. revert H0. induction H. intros.
    apply (gfp_fp divergesF) in H0 as (? & ? & ?). apply H in H0. destruct H0; eauto.
    destruct DIV. apply H2 in H1 as (? & ? & ?). eauto.
  - subst. apply sim_fp in H. apply H.
Qed.

End WithOpts.
End WithLTS.
