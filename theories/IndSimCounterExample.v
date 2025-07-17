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
From CTree Require Import CTree Eq.
From Sims Require Import Utils LTS Divergence Sims IndSim CTree.

Import CoindNotations.
Import CTreeNotations.

CoFixpoint t : ctree void1 (B2 +' B3) bool := brS3 t (Ret true) (Ret false).
CoFixpoint u' r : ctree void1 (B2 +' B3) bool := brS2 (u' r) (Ret r).
Definition u : ctree void1 (B2 +' B3) bool := brS branch2 u'.

Lemma unfold_t : t ≅ brS3 t (Ret true) (Ret false). Proof. now step. Qed.
Lemma unfold_u' r : u' r ≅ brS2 (u' r) (Ret r). Proof. now step. Qed.

Lemma transs_u' : forall x t, (trans (lts := lts) tau)^* (u' x) t ->
  t ≅ u' x \/ t ≅ Ret x.
Proof.
  intros ? t ?.
  pose (s := u' x). change (u' x) with s in H.
  assert (s ≅ u' x) by reflexivity. revert H0.
  eapply srel_str_ind_r' with (i := trans tau) (P := fun s t => s ≅ u' x -> (t ≅ u' x \/ t ≅ Ret x)).
  4: apply H.
  - cbn. intros. subs. now apply H2.
  - intros. cbn in H0. subs. now left.
  - intros. subs. destruct (H0 ltac:(reflexivity)).
    + subs. rewrite unfold_u' in H1.
      apply trans_brS_inv in H1 as ([] & ? & _); auto.
    + subs. cbn in H1. inv_trans.
Qed.

Lemma negb_ret_u' : forall x, isim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay (Ret (negb x)) (u' x) -> False.
Proof.
  intros. apply (gfp_fp (isimF _ _ _)) in H.
  remember (Ret (negb x)). remember (u' x). induction H. subst.
  destruct H as (? & _ & _). specialize (H (oval (negb x)) Stuck).
  lapply H. 2: { cbn. apply trans_ret. }
  clear H. intro. destruct H.
  - destruct TR as [t TR TR'].
    apply transs_u' in TR as [].
    + subs. rewrite unfold_u' in TR'. cbn in TR'. destruct o'; inv_trans.
    + subs. cbn in TR'. destruct o'; inv_trans.
      inv EQl. invert. inv OBS. invert. destruct x0; discriminate.
Qed.

Lemma negb_ret_ret : forall x, isim (lts := lts (E := void1) (B := B2 +' B3)) SimOpt.freeze_div SimOpt.nolock SimOpt.delay (Ret (negb x)) (Ret x) -> False.
Proof.
  intros x SIM.
  step in SIM. destruct SIM. destruct H as (? & _ & _).
  specialize (H (oval (negb x)) Stuck).
  lapply H. 2: { apply trans_ret. }
  intros []. red in TR. destruct TR.
  rewrite str_unfold_l in H0. destruct H0.
  2: { destruct H0. cbn in H0. inv_trans. }
  cbn in H0. rewrite <- H0 in H1. cbn in H1. destruct o'; inv_trans.
  inv EQl. invert. inv OBS. invert. now destruct x0.
Qed.

Lemma t_u' : forall x, isim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay t (u' x) -> False.
Proof.
  intros. apply (gfp_fp (isimF _ _ _)) in H.
  remember t. remember (u' x). destruct H. subst.
  destruct H as (_ & ? & _). specialize (H (Ret (negb x))).
  lapply H. 2: { cbn. rewrite unfold_t. eapply trans_br with (x := match x with true => t33 | false => t32 end). 2: reflexivity. destruct x; etrans. }
  clear H. intro. destruct H.
  - rewrite unfold_u' in TR. apply trans_brS_inv in TR as ([] & ? & _); subs.
    + now eapply negb_ret_u' in SIM.
    + now apply negb_ret_ret in SIM.
  - discriminate.
  - now apply negb_ret_u' in SIM.
  - rewrite str_itr' in TR.
    apply transs_u' in TR as []; subs.
    + now apply negb_ret_u' in SIM.
    + now apply negb_ret_ret in SIM.
Qed.

Goal isim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay t u -> False.
Proof.
  intros. apply (gfp_fp (isimF _ _ _)) in H.
  remember t. remember u. induction H. subst.
  destruct H as (_ & ? & _). specialize (H t).
  lapply H. 2: { cbn. rewrite unfold_t at 1. apply trans_brS31. }
  clear H. intro. destruct H.
  - apply trans_br_inv in TR as [].
    apply trans_step_inv in H as [? _]. rewrite H in SIM.
    clear t' H.
    now apply t_u' in SIM.
  - discriminate.
  - destruct DIV. now apply H1.
  - rewrite itr_str_l in TR. destruct TR.
    apply trans_br_inv in H0 as [].
    apply trans_step_inv in H0 as [? _]. rewrite H0 in H1.
    apply transs_u' in H1 as []; subs.
    + now apply t_u' in SIM.
    + step in SIM. destruct SIM. destruct H0 as (_ & ? & _).
      specialize (H0 (Ret (negb x0))).
      lapply H0. 2: { rewrite unfold_t. cbn. destruct x0; etrans. }
      clear H0. intros [].
      * cbn in TR. inv_trans.
      * discriminate.
      * now apply negb_ret_ret in SIM.
      * rewrite itr_str_l in TR. destruct TR. cbn in H1. inv_trans.
Qed.

Lemma u_div : diverges (lts := lts) u.
Proof.
  red. coinduction R CH.
  exists (u' true). split.
  - unfold u. apply trans_brS.
  - accumulate R'. exists (u' true).
    split; auto. rewrite unfold_u' at 1.
    apply trans_brS21.
Qed.

Goal sim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay true t u.
Proof.
  red. coinduction R CH.
  rewrite unfold_t. unfold u.
  cbn. constructor. repeat split; intros.
  3: now left.
  { cbn in H. destruct o; inv_trans. }
  cbn in H. apply trans_brS_inv in H as (? & ? & _).
  subs. destruct x.
  - apply tau_div; auto.
    apply (gfp_chain R).
    apply diverges_divpres.
    apply u_div.
  - eapply tau_delay; auto.
    2: apply (upto_refl (lts := lts)); auto.
    rewrite itr_str_l.
    unfold branchS.
    esplit. eapply trans_br with (x := true). 2: reflexivity. apply trans_step.
    rewrite unfold_u'. rewrite <- str_ext. eapply trans_br with (x := false).
    2: reflexivity. apply trans_step.
  - eapply tau_delay; auto.
    2: apply (upto_refl (lts := lts)); auto.
    rewrite itr_str_l.
    unfold branchS.
    esplit. eapply trans_br with (x := false). 2: reflexivity. apply trans_step.
    rewrite unfold_u'. rewrite <- str_ext. eapply trans_br with (x := false).
    2: reflexivity. apply trans_step.
Qed.
