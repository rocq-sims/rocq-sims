From Coq Require Import Program.Equality.
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
From Sims Require Import Utils LTS Sims IndSim.

Import CoindNotations.

Variant free {S St} (tr : @label S -> srel St St) : label -> (option S * St) -> (option S * St) -> Prop :=
(* insert a tau transition before observable transitions *)
| ftr_pre o st st' : tr (obs o) st st' -> free tr tau (None, st) (Some o, st')
(* then perform the actual observable transition *)
| ftr_vis o st st' : St.(Eq) st st' -> free tr (obs o) (Some o, st) (None, st')
(* keep tau transitions as is *)
| ftr_tau st st' : tr tau st st' -> free tr tau (None, st) (None, st')
.

Program Definition freesimize (lts : LTS) := {|
  Observable := lts.(Observable);
  St := {| type_of := (option lts.(Observable) * lts.(St))%type; Eq := fun '(b, st) '(b', st') => b = b' /\ lts.(St).(Eq) st st' |};
  trans := fun l => {| hrel_of := free lts.(trans) l |};
  Robs := lts.(Robs);
|}.
Next Obligation.
  constructor.
  - cbn. intros []. auto.
  - cbn. intros [] []. intuition.
  - cbn. intros [] [] []. intuition. now subst. etransitivity; eauto.
Qed.
Next Obligation.
  split; intro.
  - dependent destruction H; constructor; now rewrite <- H1, <- H2.
  - dependent destruction H; constructor; now rewrite H1, H2.
Qed.

#[export] Instance freesimize_eq : forall {lts},
  Proper (eq ==> lts.(St).(Eq) ==> (freesimize lts).(St).(Eq)) pair.
Proof.
  cbn. intros. subst. auto.
Qed.

Section WithLTS.

Context {lts : LTS}.
Notation Observable := lts.(Observable).
Notation St := lts.(St).
Notation trans := lts.(trans).
Notation Robs := lts.(Robs).
Notation label := (@label Observable).

Context (Robs_eq : Robs = eq).

Variant isimIndF R Rind s t : Prop :=
| isim_tau_l : is_tau_state s ->
  (forall s', trans tau s s' -> Rind s' t \/ (is_tau_state t /\ exists t', trans tau t t' /\ R s' t')) ->
  isimIndF R Rind s t
| isim_tau_r t' : is_tau_state t -> trans tau t t' -> Rind s t' ->
  isimIndF R Rind s t
| isim_obs : is_obs_state s -> is_obs_state t ->
  (forall o s', trans (obs o) s s' -> exists t', trans (obs o) t t' /\ R s' t') ->
  isimIndF R Rind s t
.

Section NoElim.
#[local] Unset Elimination Schemes.
Inductive isimInd R s t : Prop :=
| isimI :
  isimIndF R (isimInd R) s t -> isimInd R s t.
End NoElim.

Definition isimInd_ind :
  forall R P : St -> St -> Prop,
       (forall s t : St,
         (isimIndF R (fun s t => isimInd R s t /\ P s t) s t) ->
        P s t) -> forall t t0 : St, isimInd R t t0 -> P t t0.
Proof.
  intros until 1. fix F 3. intros. apply H. destruct H0 as [[]].
  - apply isim_tau_l; auto. intros. apply H1 in H2 as []; auto.
  - eapply isim_tau_r; eauto.
  - apply isim_obs; auto.
Qed.

Lemma isimInd_mon : forall R R', R <= R' -> isimInd R <= isimInd R'.
Proof.
  cbn. intros. induction H0. constructor. destruct H0.
  - constructor 1; auto. intros. apply H1 in H2 as [[] | (? & ? & ? & ?)]; eauto 6.
  - destruct H2. econstructor 2; eauto.
  - constructor 3; auto. intros. apply H2 in H3 as (? & ? & ?). eauto.
Qed.

Program Definition isimF : mon (St -> St -> Prop) :=
{| body R s t := isimInd R s t |}.
Next Obligation.
  eapply isimInd_mon. 2: apply H0.
  cbn. apply H.
Qed.

#[export] Instance Chain_isimF_eq : forall (R : Chain isimF),
  Proper (Eq St ==> Eq St ==> impl) `R.
Proof.
  intro. apply tower. {
    intros ? INC ?????????. eapply INC; eauto.
  }
  intros. cbn. intros; subst.
  revert y y0 H0 H1. induction H2. intros. constructor. destruct H0.
  - rewrite H1 in H0. constructor 1; auto.
    intros. rewrite <- H1 in H4. apply H3 in H4 as [[] | (? & ? & ? & ?)]; auto.
    rewrite H2 in *. eauto.
  - rewrite H2 in *. econstructor 2; eauto. now apply H4.
  - rewrite H1 in H0. rewrite H2 in H3. constructor 3; auto.
    intros. rewrite <- H1 in H5. apply H4 in H5 as (? & ? & ?).
    rewrite H2 in H5. eauto.
Qed.

#[export] Instance bchain_isimF_eq : forall (R : Chain isimF),
  Proper (Eq St ==> Eq St ==> impl) (isimInd `R).
Proof.
  intros.
  assert (Proper (Eq St ==> Eq St ==> impl) (isimF `R)).
  { typeclasses eauto. }
  cbn in H. cbn. apply H.
Qed.

Definition isim' := gfp isimF.

#[export] Instance isim'_eq :
  Proper (Eq St ==> Eq St ==> impl) isim'.
Proof.
  cbn. intros. eapply Chain_isimF_eq; eauto.
Qed.

Lemma upto_tau_r : forall (TAU : forall st st', trans tau st st' -> is_tau_state st) (R : Chain isimF) s t t',
  (trans tau)^* t t' ->
  `R s t' ->
  `R s t.
Proof.
  intros ??. apply tower. {
    intros ?????????. eapply H; eauto.
  }
  clear R. intros R **.
  revert H1. eapply srel_str_ind_l' with (i := trans tau) (P := fun t t' => isimF ` R s t' -> isimF ` R s t); auto.
  - cbn. intros. rewrite <- H1. apply H3. now rewrite H2.
  - intros. now rewrite H1.
  - intros. constructor. eapply isim_tau_r.
    eapply TAU. apply H1.
    apply H1. apply H2. apply H3.
Qed.

Theorem isim_indsim : forall s t,
  isim' s t ->
  IndSim.isim SimOpt.freeze_div SimOpt.nolock SimOpt.delay s t.
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp isimF) in H. induction H.
  destruct H.
  - constructor. repeat split; intros.
    + now apply H in H1.
    + apply H0 in H1 as [[] | (? & ? & ? & ?)]; esim.
      apply tau_div; esim. apply CH. apply (gfp_fp isimF). apply H1.
    + now left.
  - eapply isim_upto_tau_r; eauto. apply H1.
  - constructor. repeat split; intros.
    + apply H1 in H2 as (? & ? & ?).
      econstructor; esim. now rewrite Robs_eq.
    + now apply H in H2.
    + now left.
Qed.

End WithLTS.

Lemma is_obs_none : forall {lts} st,
  is_obs_state (lts := freesimize lts) (None, st) -> is_stuck st.
Proof.
  red. intros. intro. destruct H0.
  destruct l.
  - apply ftr_pre in H0. now apply H in H0.
  - apply ftr_tau in H0. now apply H in H0.
Qed.

Lemma is_obs_some : forall {lts} o st,
  is_obs_state (lts := freesimize lts) (Some o, st).
Proof.
  red. intros.
  inversion H. subst. reflexivity.
Qed.

Lemma is_tau_none : forall {lts} st,
  is_tau_state (lts := freesimize lts) (None, st).
Proof.
  red. intros.
  inversion H; now subst.
Qed.

Lemma is_tau_some : forall {lts} o st,
  is_tau_state (lts := freesimize lts) (Some o, st) -> False.
Proof.
  intros. red in H. now specialize (H _ _ ltac:(now apply ftr_vis)).
Qed.

Lemma freesimize_tau :
  forall {lts} st st', trans (lts := freesimize lts) tau st st' -> is_tau_state st.
Proof.
  intros. inversion H; subst; apply is_tau_none.
Qed.

Lemma taustar_freesimize :
  forall {lts} st st',
  (trans (lts := lts) tau)^* st st' ->
  (trans (lts := freesimize lts) tau)^* (None, st) (None, st').
Proof.
  intros.
  eapply srel_str_ind_l' with (i := trans tau) (P := fun st st' => (trans (lts := freesimize lts) tau)^* (None, st) (None, st')); auto.
  - cbn -[freesimize str]. intros.
    eapply srel_Eq. 3: apply H2.
    cbn. split; auto. now symmetry.
    cbn. split; auto. now symmetry.
  - intros. rewrite <- str_refl. split; auto.
  - intros. rewrite str_unfold_l. right.
    esplit; eauto. now constructor.
Qed.

Lemma taustar_freesimize_inv :
  forall {lts} st st',
  (trans (lts := freesimize lts) tau)^* (None, st) (None, st') ->
  (trans (lts := lts) tau)^* st st'.
Proof.
  intros.
  remember (None, st) as fst. remember (None, st') as fst'.
  revert st st' Heqfst Heqfst'.
  eapply srel_str_ind_r' with (i := trans (lts := freesimize lts) tau) (P := fun fst fst' => forall st st' : St lts, fst = (None, st) ->  fst' = (None, st') -> (trans tau)^* st st'); auto.
  - cbn -[freesimize str]. intros. subst.
    destruct x, x0. destruct H0, H1. subst.
    rewrite <- H3, <- H4. now apply H2.
  - intros. subst. rewrite <- str_refl. now destruct H0.
  - intros. subst. rewrite str_unfold_r. right.
    inversion H1; subst.
    esplit; eauto.
Qed.

Theorem indsim_isim {lts} (Robs_eq : lts.(Robs) = eq) : forall o s t,
  IndSim.isim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay s t ->
  isim' (lts := freesimize lts) (o, s) (o, t).
Proof.
  red. coinduction R CH. intros. assert (H' := H).
  apply (gfp_fp (IndSim.isimF _ _ _)) in H. induction H. destruct H as (? & ? & ?).
  destruct o.
  - constructor. apply isim_obs.
    1,2: apply is_obs_some.
    intros. inversion H2. subst.
    exists (None, t). split.
    apply ftr_vis. reflexivity. apply CH. rewrite <- H7. apply H'.
  - do 2 constructor. apply is_tau_none.
    intros. inversion H2; subst.
    + (* observable event *)
      left. assert (isimF `R (Some o, st') (None, t)). 2: apply H3.
      apply H in H4 as []. destruct TR.
      eapply upto_tau_r; auto.
      * apply freesimize_tau.
      * apply taustar_freesimize; eauto.
      * cbn. constructor.
        eapply isim_tau_r. apply is_tau_none.
        constructor. apply H4.
        constructor. eapply isim_obs. 1,2: apply is_obs_some.
        intros. rewrite Robs_eq in OBS. subst.
        inversion H5. subst.
        exists (None, t'). split. econstructor. reflexivity.
        apply CH. now rewrite <- H10.
    + (* tau transition *)
      apply H0 in H4 as [].
      * right. split. apply is_tau_none.
        exists (None, t'). split; auto.
        now constructor.
      * discriminate.
      * left. apply DIV. apply SIM.
      * right. split. apply is_tau_none.
        rewrite itr_str_l in TR. destruct TR.
        exists (None, x). split. now constructor.
        eapply upto_tau_r.
        --apply freesimize_tau.
        --instantiate (1 := (None, t')). apply taustar_freesimize; eauto.
        --apply CH. apply SIM.
Qed.

Lemma isim_obs_inv :
  forall {lts} s t o o',
  isim' (lts := freesimize lts) (Some o, s) (Some o', t) ->
  o = o' /\ isim' (lts := freesimize lts) (None, s) (None, t).
Proof.
  intros. apply (gfp_fp isimF) in H. destruct H as [[]].
  1,2: now apply is_tau_some in H.
  specialize (H1 _ _ ltac:(now apply ftr_vis)).
  destruct H1 as (? & ? & ?).
  inversion H1. subst.
  split; auto. now rewrite H7.
Qed.

Lemma isim_obs_l_inv :
  forall {lts} s t o,
  isim' (lts := freesimize lts) (Some o, s) (None, t) ->
  exists t', (trans (lts := freesimize lts) tau)^* (None, t) (Some o, t') /\ isim' (lts := freesimize lts) (Some o, s) (Some o, t').
Proof.
  intros. apply (gfp_fp isimF) in H.
  remember (Some o, s) as fs. remember (None, t) as ft.
  revert s t Heqfs Heqft. induction H. intros. subst.
  destruct H.
  - now apply is_tau_some in H.
  - destruct H1.
    inversion H0; subst.
    + destruct H1. destruct H1.
      * now apply is_tau_some in H1.
      * now apply is_tau_some in H1.
      * specialize (H5 o (None, s0)). lapply H5. 2: { now constructor. }
        clear H5; intros (? & ? & ?).
        inversion H5. subst.
        exists st'. split.
        rewrite <- str_ext. now constructor.
        apply (gfp_fp isimF). constructor. apply isim_obs.
        1,2: apply is_obs_some. intros. inversion H7. subst.
        exists (None, st'0). split; auto.
        now rewrite <- H13.
    + specialize (H2 s0 st' eq_refl eq_refl).
      destruct H2 as (? & ? & ?).
      exists x. split; auto.
      rewrite str_unfold_l. right.
      esplit; eauto.
  - specialize (H1 o (None, s0) ltac:(now apply ftr_vis)).
    destruct H1 as (? & ? & ?).
    inversion H1.
Qed.

(* very ugly, probably because of a bad induction hypothesis *)
Theorem isim_indsim' {lts} (Robs_eq : lts.(Robs) = eq) : forall s t,
  isim' (lts := freesimize lts) (None, s) (None, t) ->
  IndSim.isim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay s t.
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp isimF) in H.
  remember (None, s) as fs. remember (None, t) as ft.
  revert s t Heqfs Heqft.
  (*assert ((fs = (None, s) /\ ft = (None, t)) \/ exists o,
    (fs = (Some o, s) /\ ft = (Some o, t)) \/
    (fs = (None, s) /\ exists s0, ft = (None, s0) /\ trans (obs o) s0 s)
  ).*)
  induction H.
  intros. subst.
  destruct H.
  - constructor. repeat split; intros.
    + apply ftr_pre in H1 as ?. apply H0 in H2 as [].
      * destruct H2 as [? _].
        apply (gfp_fp isimF) in H2.
        apply isim_obs_l_inv in H2 as (? & ? & ?).
        rewrite str_unfold_r in H2. destruct H2.
        { now inversion H2. }
        destruct H2. inversion H4. subst.
        econstructor. red. esplit. eapply taustar_freesimize_inv; eauto.
        apply H8. apply CH. now apply isim_obs_inv in H3 as [_ ?]. now rewrite Robs_eq.
      * destruct H2 as (? & ? & ? & ?). inversion H3; subst.
        --apply isim_obs_inv in H4 as [<- ?].
          econstructor. apply trans_dtrans. apply H6.
          now apply CH. now rewrite Robs_eq.
        --apply isim_obs_l_inv in H4 as (? & ? & ?).
          rewrite str_unfold_r in H4. destruct H4.
          { now inversion H4. }
          destruct H4. inversion H7. subst.
          econstructor. red. esplit. rewrite str_unfold_l.
          right. esplit; eauto. eapply taustar_freesimize_inv; eauto.
          apply H11. apply CH. now apply isim_obs_inv in H5 as [_ ?]. now rewrite Robs_eq.
    + pose proof (H1' := H1). apply ftr_tau in H1. apply H0 in H1. destruct H1.
      * destruct H1. apply tau_div; auto. apply CH. apply (gfp_fp isimF) in H1. apply H1.
        apply H2; auto.
      * destruct H1 as (? & ? & ? & ?).
        inversion H2; subst.
        --apply tau_idiv; auto.
          apply (gfp_fp isimF) in H3.
          remember (None, s') as fs'. remember (Some o, st') as fst'.
          clear H1'. revert s' o st' Heqfs' Heqfst' H5.
          induction H3. intros. subst.
          destruct H3.
          ++constructor. repeat split; intros.
            **specialize (H4 (Some o0, s'0) ltac:(now apply ftr_pre)).
              destruct H4.
              --- destruct H4. apply (gfp_fp isimF) in H4.  apply isim_obs_inv in H4 as [-> ?].
                  econstructor; eauto. apply trans_dtrans. apply H5. now rewrite Robs_eq.
              --- destruct H4. now apply is_tau_some in H4.
            **specialize (H4 (None, s'0) ltac:(now apply ftr_tau)).
              destruct H4.
              --- destruct H4. specialize (H7 H2 s'0 o st' eq_refl eq_refl H5).
                  apply tau_idiv; auto.
              --- destruct H4. now apply is_tau_some in H4.
            ** now left.
          ++now apply is_tau_some in H3.
          ++apply is_obs_none in H3.
            repeat split.
            **intros. exfalso. apply H3. eexists; eauto.
            **intros. exfalso. apply H3. eexists; eauto.
            **now left.
        --eapply tau_exact. apply H5. apply CH. apply H3.
    + now left.
  - destruct H1.
    inversion H0; subst.
    + remember (None, s0) as fs0. remember (Some o, st') as fst'.
      clear H4.
      revert s0 o st' Heqfs0 Heqfst'. induction H1. intros. subst.
          destruct H1.
          ++constructor. repeat split; intros.
            **specialize (H3 (Some o0, s') ltac:(now apply ftr_pre)).
              destruct H3.
              --- destruct H3. apply (gfp_fp isimF) in H3. apply isim_obs_inv in H3 as [-> ?].
                  inversion H0. subst.
                  econstructor; eauto. apply trans_dtrans. apply H9. now rewrite Robs_eq.
              --- destruct H3. now apply is_tau_some in H3.
            **specialize (H3 (None, s') ltac:(now apply ftr_tau)).
              destruct H3.
              --- destruct H3. lapply H5. 2: { intros. inversion Heqft. }
                  clear H5. intro. specialize (H5 H0 s' o st' eq_refl eq_refl).
                  apply tau_idiv; auto.
              --- destruct H3. now apply is_tau_some in H3.
            ** now left.
          ++now apply is_tau_some in H1.
          ++apply is_obs_none in H1.
            repeat split.
            **intros. exfalso. apply H1. eexists; eauto.
            **intros. exfalso. apply H1. eexists; eauto.
            **now left.
    + eapply isim_upto_tau_r; eauto. apply H2; auto.
  - constructor. repeat split.
    + intros. eapply ftr_pre in H2. now apply H in H2.
    + intros. eapply ftr_tau in H2. now apply H in H2.
    + now left.
Qed.
