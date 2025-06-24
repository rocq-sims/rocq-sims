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
From OptSim Require Import Utils LTS OptSim.

Import CoindNotations.


Section WithLTS.

Context {lts : LTS}.
Context (freeze : SimOpt.freeze_opt) (lock : SimOpt.lock_opt) (delay : SimOpt.delay_opt).
Notation Observable := lts.(Observable).
Notation St := lts.(St).
Notation trans := lts.(trans).
(*Notation epsilon := lts.(epsilon).*)
Notation Robs := lts.(Robs).
Notation ub_state := lts.(ub_state).
Notation label := (@label Observable).

Definition simIndF R Rind s t :=
  (forall o s', trans (obs o) s s' ->
    ObsAnswer delay R s' t o
  ) /\
  (forall s', trans tau s s' ->
    TauAnswer freeze delay R Rind s' t
  ) /\
  (lock = SimOpt.nolock \/ (is_stuck s -> can_be_stuck delay t)).

Section NoElim.
#[local] Unset Elimination Schemes.
Inductive simInd R s t : Prop :=
| simI :
  simIndF R (simInd R) s t -> simInd R s t.
End NoElim.

Definition simInd_ind :
  forall R P : St -> St -> Prop,
       (forall s t : St,
         (simIndF R (fun s t => simInd R s t /\ P s t) s t) ->
        P s t) -> forall t t0 : St, simInd R t t0 -> P t t0.
Proof.
  intros until 1. fix F 3. intros. apply H. destruct H0. repeat split; intros.
  - apply H0 in H1 as [].
    econstructor; eauto.
  - apply H0 in H1 as []; esim.
  - apply H0.
Qed.

Lemma simInd_mon : forall R R', R <= R' -> simInd R <= simInd R'.
Proof.
  cbn. intros. induction H0.
  repeat split; intros.
  - apply H0 in H1 as []; esim.
  - apply H0 in H1 as []; esim.
    destruct DIV. esim.
  - apply H0.
Qed.

Program Definition isimF : mon (St -> St -> Prop) :=
{| body R s t := simInd R s t |}.
Next Obligation.
  eapply simInd_mon. 2: apply H0.
  cbn. apply H.
Qed.

#[export] Instance Chain_isimF_eq : forall (R : Chain isimF),
  Proper (Eq St ==> Eq St ==> impl) `R.
Proof.
  intro. apply tower. {
    intros ? INC ?????????. eapply INC; eauto.
  }
  intros. cbn. intros; subst.
  revert y y0 H0 H1. induction H2. intros.
  repeat split; intros.
  - rewrite <- H2. rewrite <- H1 in H3. now apply H0 in H3.
  - rewrite <- H1 in H3. apply H0 in H3 as []; rewrite ?H2 in *; esim.
    apply tau_div; auto. now eapply DIV.
  - rewrite <- H1, <- H2. apply H0.
Qed.

Definition isim := gfp isimF.

Lemma tau_idiv : forall (R : Chain isimF) s' t,
  freeze = SimOpt.freeze_div ->
  isimF `R s' t ->
  TauAnswer freeze delay `R (simInd `R) s' t.
Proof.
  intros. apply tau_div; auto. now step.
Qed.

Theorem sim_indsim : forall s t ,
  isim s t ->
  sim freeze lock delay true s t.
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp isimF) in H. induction H.
  apply simF_equiv. repeat split; intros.
  - apply H in H0 as []; esim.
  - apply H in H0 as []; esim.
    apply tau_div; auto. apply simF_f_t. now rewrite H0. apply DIV.
  - apply H.
Qed.

Lemma isim_upto_tau_r (Hdelay : delay = SimOpt.delay) : forall (R : Chain isimF) s t t',
  trans tau t t' ->
  `R s t' ->
  `R s t.
Proof.
  intro. apply tower. {
    intros ?????????. eapply H; eauto.
  }
  clear R. intros R **. induction H1. repeat split; intros.
  - apply H1 in H2 as []. econstructor; eauto. red in TR |- *. rewrite Hdelay in *.
    rewrite str_unfold_l, dotplsx, <- dotA. right. esplit; eauto.
  - apply H1 in H2 as []; esim.
    eapply tau_delay; eauto. rewrite itr_unfold_l. right. esplit; eauto.
  - destruct H1 as (_ & _ & []); auto.
    right. intro. apply H1 in H2. eapply can_be_stuck_taustar; eauto. now rewrite <- str_ext.
Qed.

End WithLTS.
