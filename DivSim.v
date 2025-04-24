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
From OptSim Require Import Utils LTS Divergence OptSim.

Section WithLTS.

Context {lts : LTS}.

Notation Observable := lts.(Observable).
Notation St := lts.(St).
Notation trans := lts.(trans).
Notation epsilon := lts.(epsilon).
Notation Robs := lts.(Robs).
Notation ub_state := lts.(ub_state).
Notation label := (@label Observable).

Program Definition divsimF lock : mon (St -> St -> Prop) :=
{|
  body := fun R s t => (forall o s', ((trans tau)^* ⋅ trans (obs o)) s s' ->
    exists o' t',
        ((trans tau)^* ⋅ trans (obs o')) t t' /\
      R s' t' /\
      Robs o o') /\
  (forall s', (trans tau)^* s s' ->
    exists t', 
      (trans tau)^* t t' /\ R s' t') /\
  (diverges s -> diverges t) /\
  (lock = SimOpt.nolock \/ (is_stuck s -> is_stuck t))
|}.
Next Obligation.
  repeat split; intros; auto.
  - apply H0 in H4 as (? & ? & ? & ? & ?). eauto 6.
  - apply H1 in H4 as (? & ? & ?). eauto.
Qed.

Definition divsim := gfp (divsimF SimOpt.nolock).

Program Definition divsimF' : mon (St -> St -> Prop) :=
{|
  body := fun R s t => (forall o s', trans (obs o) s s' ->
    exists o' t',
        ((trans tau)^* ⋅ trans (obs o')) t t' /\
      R s' t' /\
      Robs o o') /\
  (forall s', trans tau s s' ->
    exists t', 
      (trans tau)^* t t' /\ R s' t') /\
  (diverges s -> diverges t)
|}.
Next Obligation.
  repeat split; intros; auto.
  - apply H0 in H3 as (? & ? & ? & ? & ?). eauto 6.
  - apply H1 in H3 as (? & ? & ?). eauto.
Qed.

Definition divsim' := gfp divsimF'.

Section WithOpts.

Context (freeze : SimOpt.freeze_opt)
  (lock : SimOpt.lock_opt) (delay : SimOpt.delay_opt).

Lemma divsim_divpres : forall s t,
  divsim s t ->
  sim freeze lock delay false s t.
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp (divsimF _)) in H. destruct H as (_ & _ & ? & _).
  destruct (diverges_lem s).
  apply H in H0. eapply chain_div in H0. apply H0; auto.
  eapply chain_nodiv with (R := R) (t := t) in H0. apply H0; auto.
Qed.

(* ok *)
Lemma divsim_equiv
  (Hfreeze : freeze = SimOpt.freeze_div)
  (Hlock : lock = SimOpt.nolock)
  (Hdelay : delay = SimOpt.delay) :
  forall b s t, divsim s t ->
  sim freeze lock delay b s t.
Proof.
  red. coinduction R CH. intros. destruct b.
  2: now apply (gfp_bchain R), divsim_divpres.
  constructor.
  repeat split; intros.
  - apply (gfp_fp (divsimF _)) in H. destruct H as (? & ? & _).
    apply trans_add_delay in H0.
    apply H in H0 as (? & ? & ? & ? & ?).
    eapply ans_delay_obs; eauto.
  - apply (gfp_fp (divsimF _)) in H.
    rewrite (str_ext (trans tau)) in H0.
    apply H in H0 as (? & ? & ?).
    rewrite str_itr in H0. destruct H0.
    + apply tau_div. assumption. apply CH. cbn in H0. admit.
      apply CH. admit.
    + eapply tau_delay; eauto.
  - now left.
Admitted.

Lemma divsim_equiv'
  (Hfreeze : freeze = SimOpt.freeze_div)
  (Hlock : lock = SimOpt.nolock)
  (Hdelay : delay = SimOpt.delay) :
  forall s t, (forall b, sim freeze lock delay b s t) ->
  divsim' s t.
Proof.
  red. coinduction R CH. intros. cbn -[dot str]. repeat split; intros.
  - specialize (H true). apply sim_fp in H. apply H in H0 as []; auto.
    + exists o', t'. split. { now apply trans_add_delay. }
      split; auto. apply CH. intros. destruct b; auto.
      now apply sim_f_t.
    + exists o', t'. repeat split; auto.
      apply CH. intros. destruct b; auto. now apply sim_f_t.
  - specialize (H true). apply sim_fp in H. apply H in H0 as []; auto.
    + exists t'. split. { now rewrite <- str_ext. }
      apply CH. intros []; auto. now apply sim_f_t.
    + now rewrite Hfreeze in H0.
    + exists t. split. { now rewrite <- str_refl. }
      apply CH. intros []; try easy.
    + exists t'. split. { now rewrite <- str_itr'. }
      apply CH. intros []; auto. now apply sim_f_t.
  - specialize (H false). revert s t H H0. clear R CH. red. coinduction R CH. intros.
    cbn. apply sim_fp in H. revert H0. induction H. intros.
    apply (gfp_fp divergesF) in H0 as (? & ? & ?). apply H in H0. destruct H0; eauto.
    destruct DIV. apply H2 in H1 as (? & ? & ?). eauto.
Qed.

End WithOpts.
End WithLTS.
