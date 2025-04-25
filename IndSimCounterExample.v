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
From OptSim Require Import Utils LTS Divergence OptSim IndSim CTree.

Import CoindNotations.
Import CTreeNotations.

CoFixpoint t : ctree void1 (B2 +' B3) bool := brS3 t (Ret true) (Ret false).
CoFixpoint u' r : ctree void1 (B2 +' B3) bool := brS2 (u' r) (Ret r).
Definition u : ctree void1 (B2 +' B3) bool := brS branch2 u'.

Lemma unfold_t : t = brS3 t (Ret true) (Ret false). Admitted.
Lemma unfold_u' r : u' r = brS2 (u' r) (Ret r). Admitted.

Lemma negb_ret_u' : forall x, isim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay (Ret (negb x)) (u' x) -> False.
Proof.
  intros. apply (gfp_fp (isimF _ _ _)) in H.
  remember (Ret (negb x)). remember (u' x). induction H. subst. rewrite unfold_u' in H.
  destruct H as (? & _ & _). specialize (H (oval (negb x)) Stuck).
  lapply H. 2: { cbn. apply trans_ret. }
  clear H. intro. destruct H.
  - apply trans_brS_inv in TR as (? & ? & ?).
    cbn in OBS. subst. discriminate.
  - admit.
Admitted.

Lemma t_u' : forall x, isim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay t (u' x) -> False.
Proof.
  intros. apply (gfp_fp (isimF _ _ _)) in H.
  remember t. remember (u' x). destruct H. subst. rewrite unfold_t, unfold_u' in H.
  destruct H as (_ & ? & _). specialize (H (Ret (negb x))).
  lapply H. 2: { cbn. eapply trans_br with (x := match x with true => t33 | false => t32 end). 2: reflexivity. destruct x; etrans. }
  clear H. intro. destruct H.
  - apply trans_brS_inv in TR as ([] & ? & _); subs.
    + now eapply negb_ret_u' in SIM.
    + admit.
  - discriminate.
  - rewrite <- unfold_u' in SIM. now apply negb_ret_u' in SIM.
  - admit.
Admitted.

Goal isim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay t u -> False.
Proof.
  intros. apply (gfp_fp (isimF _ _ _)) in H.
  remember t. remember u. induction H. subst. rewrite unfold_t in H. unfold u in H.
  destruct H as (_ & ? & _). specialize (H t).
  lapply H. 2: { cbn. apply trans_brS31. }
  clear H. intro. destruct H.
  - apply trans_br_inv in TR as [].
    apply trans_step_inv in H as [? _]. rewrite H in SIM.
    clear t' H.
    now apply t_u' in SIM.
  - discriminate.
  - destruct DIV. apply H1. apply unfold_t. reflexivity.
  - admit.
Admitted.

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
  1, 3: admit.
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
  - admit.
Admitted.
