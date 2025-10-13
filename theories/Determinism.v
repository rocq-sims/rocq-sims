From Coq Require Import List.
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
From Sims Require Import Utils LTS Sims LTSSum UB Divergence DivSim.

Import CoindNotations.

Record LblEqCorrect {O} (LblRel : relation (@label O)) := {
  Equivalence_LblRel : Equivalence LblRel;
  RespectsTau : forall lbl, LblRel tau lbl -> lbl = tau
}.

(* State st is deterministic *)
Definition deterministic {lts} (st : lts.(St)) :=
  forall (l : label) st' st'',
  trans l st st' ->
  trans l st st'' ->
  st' = st''.

(* State St has outgoing transitions labelled with labels from the same equivalence class *)
(* this holds in the LTS with no UBs *)
Definition consistent_labels {lts}
  (LblEq : relation label) (st : lts.(St)) :=
  forall l l' st' st'',
  trans l st st' ->
  trans l' st st'' ->
  LblEq l l'.

Definition determinate lts (LblEq : relation label) `{LblEqCorrect LblEq} :=
  forall (st : lts.(St)), deterministic st /\ consistent_labels LblEq st.

(* If state St has one transition from an equivalence class, it has all of them. *)
Definition receptive {lts}
  (LblEq : relation label) (st : lts.(St)) :=
  forall l st',
  trans l st st' ->
  forall l',
  LblEq l l' ->
  exists st'', trans l' st st''.

#[export] Instance consistent_labels_eq :
  forall {lts} (LblEq : relation label),
  Proper (lts.(St).(Eq) ==> impl) (consistent_labels LblEq).
Proof.
  cbn. red. intros. rewrite <- H in H1, H2. eapply H0; eauto.
Qed.

#[export] Instance deterministic_eq :
  forall {lts},
  Proper (lts.(St).(Eq) ==> impl) deterministic.
Proof.
  cbn. red. intros. rewrite <- H in H1, H2. eapply H0; eauto.
Qed.

Lemma consistent_labels_is_obs_state : forall {lts}
  (LblEq : relation label) `{LblEqCorrect LblEq} o (st st' : lts.(St)),
  consistent_labels LblEq st ->
  trans (obs o) st st' ->
  is_obs_state st.
Proof.
  red. intros. eapply H in H1. apply H1 in H0 as ?.
  destruct l; auto.
  now apply LblEqCorrect0.(RespectsTau _) in H2.
Qed.

Lemma sim_diverges_determinate : forall {lts}
  (LblEq : relation label) `{LblEqCorrect LblEq} (Robs_eq : lts.(Robs) = eq)
  (src tgt : lts.(St)),
  From deterministic tgt ->
  From (consistent_labels LblEq) tgt ->
  diverges src ->
  diverges tgt ->
  sim (lts := ubify lts is_stuck _) SimOpt.freeze_div SimOpt.nolock SimOpt.delay
    true tgt src.
Proof.
  intros ????. red. coinduction R CH. intros.
  apply simF_equiv. repeat split; intros. 3: now left.
  - apply (gfp_fp divergesF) in H2 as (? & ? & ?).
    inversion H3; subst; clear H3. 2: { esim. }
    eapply (from_id H0) in H2. apply H2 in H6. now apply LblEqCorrect0.(RespectsTau _) in H6.
  - apply (gfp_fp divergesF) in H2 as (? & ? & ?).
    inversion H3; subst; clear H3. 2: { esim. }
    apply (gfp_fp (fromF _)) in H as [].
    eapply H in H5 as ?. apply H6 in H2 as <-. clear H6.
    apply (gfp_fp divergesF) in H1 as (? & ? & ?).
    eapply tau_exact. { apply utrans_tau_, H1. }
    apply CH; auto. eapply H3; eauto. esim.
Qed.


(* 'transdet l st st': st ->l st' is the only transition of st. *)

Program Definition transdet {lts} l : srel _ _ :=
  {| hrel_of := fun st st' =>
    trans (lts := lts) l st st' /\ forall l' st'', trans l' st st'' -> l = l' /\ lts.(St).(Eq) st' st'' |}.
Next Obligation.
  split; intros [].
  - rewrite H, H0 in H1. split; auto. intros.
    rewrite <- H in H3. apply H2 in H3 as [<- <-]. split; auto. now symmetry.
  - rewrite <- H, <- H0 in H1. split; auto. intros.
    rewrite H in H3. apply H2 in H3 as [<- <-]. split; auto.
Qed.

Lemma upto_taudet_l :
  forall {lts} lock delay (R : Chain (simF SimOpt.freeze_div lock delay)) (s s' t : lts.(St)),
  (transdet tau)^* s s' ->
  `R true s' t ->
  `R true s t.
Proof.
  intros ?????.
  intros ???. eapply srel_str_ind_l' with (P := fun s s' => `R true s' t -> `R true s t).
  4: apply H. all: clear.
  - cbn. intros. rewrite <- H. rewrite <- H0 in H2. auto.
  - intros. now rewrite H.
  - intros. destruct H. eapply upto_tau_l.
    + red. intros. now apply H2 in H3 as [<- _].
    + right. esim.
    + intros. apply H2 in H3 as [_ ?]. rewrite <- H3. auto.
Qed.

Lemma determinate_trans_transdet : forall {lts}
  (LblEq : relation label) `{LblEqCorrect LblEq}
  (st st' : lts.(St)),
  From (consistent_labels LblEq) st ->
  From deterministic st ->
  (trans tau)^* st st' ->
  (transdet tau)^* st st'.
Proof.
  intros. revert H H0.
  eapply srel_str_ind_l' with (P := fun st st' => From (consistent_labels LblEq) st ->
    From deterministic st -> (transdet tau)^* st st').
  4: apply H1.
  - cbn -[str]. intros. rewrite <- H, <- H0. apply H2. all: now rewrite H.
  - intros. now rewrite H, <- str_refl.
  - intros. rewrite str_unfold_l. right.
    esplit.
    + split; eauto. intros.
      apply from_id in H2, H3.
      eapply H2 in H as ?. apply H5 in H4 as ?. apply LblEqCorrect0.(RespectsTau _) in H6 as ->.
      split; auto.
      eapply H3 in H. apply H in H4 as ->. reflexivity.
    + simple eapply from_trans in H2, H3; eauto.
Qed.

Lemma ub_taustar_det : forall {lts} (st st' : lts.(St))
  ubs (Hubs : Proper (lts.(St).(Eq) ==> iff) ubs) (Hubs' : forall st st', ubs st -> ~trans tau st st'),
  (transdet (lts := lts) tau)^* st st' ->
  (transdet (lts := ubify lts ubs Hubs) tau)^* st st'.
Proof.
  intros. revert H. intro. eapply srel_str_ind_l' with (P := fun st st' =>
    (transdet (lts := ubify lts ubs Hubs) tau)^* st st'); eauto.
  - cbn -[str]. intros. now rewrite <- H0, <- H1.
  - intros. rewrite H0. now rewrite <- str_refl.
  - intros. rewrite str_unfold_l. right. esplit; eauto.
    split. apply utrans_tau_. apply H0.
    intros. inversion H2; subst; clear H2.
    + now apply H0 in H3.
    + split; eauto. apply H0 in H3 as []. apply H3.
    + exfalso. eapply Hubs' in H3. apply H3. apply H0.
Qed.

Lemma taustar_det_obs : forall {lts} (st st1 st1' st2 : lts.(St)) o,
  (trans tau)^* st st1 ->
  (transdet tau)^* st st2 ->
  is_obs_state st2 ->
  trans (obs o) st1 st1' ->
  lts.(St).(Eq) st1 st2.
Proof.
  intros.
  revert H0 H1 H2.
  eapply srel_str_ind_l' with (P := fun st st1 => (transdet tau)^* st st2 ->
is_obs_state st2 -> trans (obs o) st1 st1' -> lts.(St).(Eq) st1 st2); eauto.
  all: clear st st1 H.
  - cbn -[str]. intros. rewrite <- H0. apply H1; auto.
    now rewrite H. now rewrite H0.
  - intros. rewrite H in H0. clear s H.
    rewrite str_unfold_l in H0. destruct H0.
    + apply H.
    + destruct H as [? [] _]. now apply H0 in H2 as [? _].
  - intros. apply H0; auto.
    rewrite str_unfold_l in H1. destruct H1.
    + cbn in H1. rewrite H1 in H. esim.
    + destruct H1. apply H1 in H as [_ ?]. rewrite H in H4.
      apply H4.
Qed.


Theorem forward_backward : forall {lts}
  (LblEq : relation label) `{LblEqCorrect LblEq} (Robs_eq : lts.(Robs) = eq)
  (src tgt : lts.(St)),
  From (receptive LblEq) src ->
  From deterministic tgt ->
  From (consistent_labels LblEq) tgt ->
  sim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay true src tgt ->
  sim (lts := ubify lts is_stuck _) SimOpt.freeze_div SimOpt.nolock SimOpt.delay
    true tgt src.
Proof.
  intros ?? LBLEQ ?. red. coinduction R CH. intros ?? REC DET CONS SIM.
  destruct (Divergence.Classical.trans_case src) as [|[]].
  - (* divergence *)
    apply (gfp_bchain R). eapply sim_diverges_determinate; eauto.
    eapply sim_diverges; eauto.
  - (* stuck (UB) *)
    apply can_be_stuck_delay in H as (? & ? & ?).
    eapply upto_tau_r; auto. instantiate (1 := x). now apply ub_taustar.
    apply simF_ub_r; auto. now rewrite Robs_eq.
  - (* the source performs an observable transition *)
    destruct H as (o & src'' & [src' TR TR']).
    (* skip the leading taus at src *)
    eapply upto_tau_r; auto. { apply ub_taustar, TR. }
    red. red.
    simple eapply from_taustar in REC; eauto.
    2: { cbn. intros. red. setoid_rewrite <- H. apply H0. }
    eapply sim_inv_taustar_l in SIM; eauto.
    clear src TR.
    (* src is receptive, thus all the labels in the equivalence class occur *)
    apply from_id in REC as REC'. specialize (REC' (obs o) src'' TR').
    (* exploit the simulation to establish that tgt can perform an observable transition *)
    apply sim_fp in SIM. apply SIM in TR' as [? ? ? _ ?]. clear src''. rewrite Robs_eq in OBS. subst o'.
    red in TR.
    (* skip the leading taus at tgt *)
    destruct TR as [tgt' TR TR'].
    eapply determinate_trans_transdet in TR as TRtau; eauto.
    eapply ub_taustar_det with (ubs := is_stuck) in TRtau as UTR. 2: { intros. esim. }
    eapply upto_taudet_l. apply UTR. clear UTR. red. red.
    simple eapply from_taustar in DET; eauto.
    simple eapply from_taustar in CONS; eauto. 2,3: typeclasses eauto.
    clear TR.
    (* exploit label consistency to restrict the simulation game *)
    apply simF_equiv. repeat split; intros.
    3: now left.
    2: {
      inversion H; subst; clear H. 2: { esim. }
      apply from_id in CONS. eapply CONS in H0. apply H0 in TR'. now eapply LBLEQ.(RespectsTau _) in TR'.
    }
    inversion H; subst; clear H; [| esim]. rename s' into tgt''.
    apply from_id in CONS as CONS'. eapply CONS' in TR'.
    (* answer the backward simulation game with a transition built from receptiveness *)
    apply REC' in TR' as (src'' & ?); eauto.
    econstructor; eauto.
    1: { apply trans_dtrans. apply utrans_obs_, H. }
    2: { cbn. now rewrite Robs_eq. }
    (* apply the coinduction hypothesis *)
    apply itr_ext_hrel.
    eapply CH; eauto. 1,2,3: eapply from_trans; eauto.
    (* establish that we still have a forward simulation using determinism *)
    apply SIM in H as []. apply itr_sim in SIM0. 2: { rewrite Robs_eq. typeclasses eauto. }
    red in TR.
    destruct TR as [tgt_ TR TR'].
    eapply taustar_det_obs in TR; eauto. 2: { eapply consistent_labels_is_obs_state; eauto. }
    rewrite TR in TR'. clear tgt_ TR.
    rewrite Robs_eq in OBS. subst l.
    apply from_id in DET. eapply DET in TR'. apply TR' in H1 as ->. apply SIM0.
Qed.
