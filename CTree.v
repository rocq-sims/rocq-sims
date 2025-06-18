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
From CTree Require Import CTree Eq Eq.Epsilon.
From OptSim Require Import (*Trace*) Utils LTS Divergence OptSim.

Import CoindNotations.


Variant olabel {E} :=
| oobs {X} : E X -> X -> olabel
| oval {X} : X -> olabel.

Definition clabel {E} (l : @LTS.label (@olabel E)) :=
  match l with
  | tau => τ
  | LTS.obs (oobs e x) => Trans.obs e x
  | LTS.obs (oval v) => val v
  end.

Program Definition lts {E B X} : LTS :=
{|
  Observable := @olabel E;
  St := @SS E B X; (* FIXME heterogeneous ctrees *)
  LTS.trans := fun l => {| hrel_of := Trans.trans (clabel l) |};
  (*epsilon := {| hrel_of := fun _ _ => False |};*)
  Robs := eq; (* FIXME heterogeneous relations *)
  ub_state := fun _ => False
|}.

#[export] Instance Chain_simF_equ {E B X} freeze lock delay b : forall (R : Chain (simF (lts := lts) freeze lock delay)),
  Proper (@equ E B X X eq ==> equ eq ==> impl) (`R b).
Proof.
  intros. cbn. intros.
  eapply (Chain_simF_eq'' (lts := lts)); eauto.
Qed.

Lemma dtrans_bind_l : forall {E B X Y} delay l (t t' : St (@lts E B X)) (k : X -> ctree E B Y)
  (LBL : ~is_val (clabel l)),
  dtrans (lts := lts) delay l t t' ->
  dtrans (lts := @lts E B Y) delay l (CTree.bind t k) (CTree.bind t' k).
Proof.
  intros. apply dtrans_case in H as [| [-> ?]].
  - apply trans_dtrans. apply trans_bind_l; auto.
  - destruct H. rewrite str_itr' in H. esplit.
    apply transs_bind_l. apply H.
    apply trans_bind_l; auto.
Qed.

(* WRONG because Br: k x is not necessarily visible *)
Lemma taustar_bind_r : forall {E B X Y} (u : St (@lts E B Y)) (t : St (@lts E B X)) (k : X -> ctree E B Y) x,
  (((trans tau)^*)⋅trans (lts := lts) (LTS.obs (oval x))) t Stuck ->
  (trans (lts := lts) tau)^* (k x) u ->
  (trans (lts := lts) tau)^* (CTree.bind t k) u.
Proof.
  (*intros. assert (wtrans τ (CTree.bind t k) u).
  2: { now apply wtrans_τ. }
  destruct H. eapply wtrans_bind_r'. eapply wconss. apply wtrans_τ. apply H. apply trans_wtrans. apply H1. Search pwtrans. eapply transs_bind
  intros. revert H0. eapply srel_str_ind_r with (i := trans tau) (P := fun u => (trans (lts := lts) tau)^* (k x) u -> (trans (lts := lts) tau)^* (CTree.bind t k) u).
  3: { rewrite <- str_refl. reflexivity. }
  3: {*)
Abort.

Lemma dtrans_bind_r : forall {E B X Y} delay l (u : St (@lts E B Y)) (t : St (@lts E B X)) (k : X -> ctree E B Y) x,
  dtrans (lts := lts) delay (LTS.obs (oval x)) t Stuck ->
  dtrans (lts := lts) delay l (k x) u ->
  dtrans delay l (CTree.bind t k) u.
Proof.
  intros. destruct delay.
  - cbn -[dot str trans].
    red in H, H0.
    intros. destruct H, H0.
    rewrite str_itr in H0.
    destruct H0.
    + esplit. apply transs_bind_l with (k := k) in H. apply H.
      eapply trans_bind_r. apply H1. cbn in H0. rewrite H0. apply H2.
    + esplit. 2: apply H2. rewrite <- str_trans. esplit.
      * apply transs_bind_l with (k := k) in H. apply H.
      * rewrite itr_str_l in H0.
        rewrite <- str_itr'.
        rewrite itr_str_l. destruct H0. esplit. 2: apply H3.
        eapply trans_bind_r. apply H1. apply H0.
  - cbn. eapply trans_bind_r. apply H. apply H0.
Qed.

Lemma tauplus_bind_l : forall {E B X Y} (t t' : St (@lts E B X)) (k : X -> ctree E B Y),
  (lts.(trans) tau)^+ t t' ->
  (lts.(trans) tau)^+ (CTree.bind t k) (CTree.bind t' k).
Proof.
  intros. apply dtrans_tauplus with (delay := SimOpt.delay).
  apply tauplus_dtrans in H.
  eapply dtrans_bind_l; eauto. apply is_val_τ.
Qed.

Lemma tauplus_bind_r : forall {E B X Y} (u : St (@lts E B Y)) (t : St (@lts E B X)) (k : X -> ctree E B Y) x,
  dtrans (lts := lts) SimOpt.delay(*FIXME*) (LTS.obs (oval x)) t Stuck ->
  (lts.(trans) tau)^+ (k x) u ->
  (lts.(trans) tau)^+ (CTree.bind t k) u.
Proof.
  intros. apply dtrans_tauplus with (delay := SimOpt.delay).
  apply tauplus_dtrans in H0.
  eapply dtrans_bind_r; eauto.
Qed.

Lemma ObsAnswer_bind_r : forall {E B X Y} delay R (s' : St (@lts E B Y)) (t : St (@lts E B X)) (k : X -> ctree E B Y) x o,
  ObsAnswer (lts := lts) delay (fun _ _ => True) Stuck t (oval x) ->
  ObsAnswer delay R s' (k x) o ->
  ObsAnswer delay R s' (CTree.bind t k) o.
Proof.
  intros. destruct H.
  cbn in OBS. subst.
  destruct H0. eapply ans_obs. eapply dtrans_bind_r; eauto.
  all: auto.
  apply dtrans_trans in TR as ?. destruct H.
  apply trans_val_inv in H0.
  now rewrite H0 in TR.
Qed.

Lemma epsilon_correct : forall {E B X} (t u : ctree E B X),
  Epsilon.epsilon t u ->
  LTS.epsilon (lts := lts) t u.
Proof.
  red. intros.
  eapply epsilon_trans; eauto.
Qed.

Lemma TauAnswer_bind_r : forall {E B X Y} freeze lock delay (R : Chain (simF freeze lock delay))
  (s' : St (@lts E B Y)) (t : St (@lts E B X)) (k : X -> ctree E B Y) x
  (Hlock : lock = SimOpt.nolock \/ forall x, extrans (lts := lts) (k x)),
  ObsAnswer (lts := lts) delay (fun _ _ => True) Stuck t (oval x) ->
  TauAnswer freeze delay (`R true) (`R false) s' (k x) ->
  TauAnswer freeze delay (`R true) (`R false) s' (CTree.bind t k).
Proof.
  intros. destruct H.
  cbn in OBS. subst. assert (t' ≅ Stuck). {
    apply dtrans_trans in TR as [].
    now apply trans_val_inv in H1.
  }
  rewrite H in TR. clear t' H.
  apply dtrans_case in TR as [TR | [-> TR]].
  - destruct H0.
    + eapply tau_exact; try eassumption. eapply trans_bind_r.
      apply TR. apply TR0.
    + apply tau_freeze; auto.
      eapply upto_epsilon_r. auto. 3: apply SIM0.
      { destruct Hlock; auto. }
      apply epsilon_correct. eapply epsilon_bind_ret.
      now apply trans_val_epsilon in TR as [].
    + apply tau_div'; auto. intro.
      eapply upto_epsilon_r. auto. 3: destruct b; eauto.
      { destruct Hlock; auto. }
      apply epsilon_correct. eapply epsilon_bind_ret.
      now apply trans_val_epsilon in TR as [].
    + eapply tau_delay; try eassumption.
      eapply tauplus_bind_r; eauto.
      apply trans_dtrans. apply TR.
  - destruct H0.
    + eapply tau_delay. auto.
      eapply tauplus_bind_r.
      * red. rewrite <- str_itr'. apply TR.
      * rewrite <- itr_ext. apply TR0.
      * apply SIM0.
    + destruct TR.
      eapply tau_delay. auto.
      eapply tauplus_bind_l; eauto.
      eapply upto_epsilon_r; eauto.
      { destruct Hlock; auto. }
      eapply epsilon_correct. eapply epsilon_bind_ret.
      apply trans_val_epsilon in H1 as []. apply H1.
    + destruct TR.
      eapply tau_delay. auto.
      eapply tauplus_bind_l; eauto.
      eapply upto_epsilon_r; eauto.
      { destruct Hlock; auto. }
      eapply epsilon_correct. eapply epsilon_bind_ret.
      apply trans_val_epsilon in H1 as []. apply H1.
    + destruct TR.
      eapply tau_delay. auto.
      eapply tauplus_bind_r; eauto.
      * esplit; eauto. rewrite <- str_itr'. apply H0.
      * apply SIM0.
Qed.

Lemma diverges_bind {E B X Y} :
  forall (t : ctree E B X) (k : X -> ctree E B Y),
  diverges (lts := lts) t ->
  diverges (lts := lts) (CTree.bind t k).
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp divergesF) in H as (? & ? & ?).
  exists (CTree.bind x k). split; auto. apply trans_bind_l; auto.
  apply is_val_τ.
Qed.

Lemma divpres_upto_bind1 {E B X Y} freeze lock delay : forall
  (R : Chain (simF (lts := lts) freeze lock delay))
  (t : ctree E B X) (k k' : X -> ctree E B Y)
  (Hlock : True(*lock = SimOpt.nolock \/ forall x, extrans (lts := lts) (k' x)*)),
  True ->
  (forall x, `R false (k x) (k' x)) ->
  `R false (CTree.bind t k) (CTree.bind t k').
Proof.
  intro. apply tower. {
    intros ??????????. apply H; auto.
    intros. now apply H1.
  }
  clear R. intros R **.
  apply simF_equiv.
  constructor. intros ??. apply trans_bind_inv in H2 as [(? & ? & ? & ?)|(? & ? & ?)].
  - subs.
    eapply dtau_match. eapply trans_bind_l; eauto. apply H; auto. intros. step. apply H1.
  - clear H0. assert (H0 : True) by apply I. specialize (H1 x). apply simF_equiv in H1.
    revert s' H3.
    assert (divpresF (`R false) (k x) (CTree.bind t k')).
    2: { apply H3. }
    remember (k x) as kx. assert (KX: (lts.(trans) tau)^* (k x) kx). { subst. now rewrite <- str_refl. } clear Heqkx.
    remember (k' x) as k'x.
    revert k k' x KX Hlock Heqk'x H2. induction H1; intros; subst.
    constructor. intros ??.
    apply H1 in H3 as ?. destruct H4.
    + eapply dtau_plus. 2: { apply DIV. }
      rewrite <- itr_ext. eapply trans_bind_r; eauto.
    + destruct DIV.
      eapply dtau_div. destruct DIV.
      eapply H5; eauto.
      rewrite str_unfold_r. right. esplit; eauto.
Qed.

Lemma divpres_upto_bind' {E B X Y} freeze lock : forall
  (R : Chain (simF (lts := lts) freeze lock SimOpt.delay))
  (t t' : ctree E B X) (k k' : X -> ctree E B Y),
  (nodiv (lts := lts) t \/ diverges (lts := lts) t') ->
  (forall x, `R false (k x) (k' x)) ->
  (forall x : X, dtrans (lts := lts) SimOpt.delay (obs (oval x)) t Stuck -> dtrans (lts := lts) SimOpt.delay (obs (oval x)) t' Stuck) ->
  `R false (CTree.bind t k) (CTree.bind t' k').
Proof.
  intro. apply tower. {
    intros ???????????. apply H; auto.
    intros. now apply H1.
  }
  clear R. intros R **.
  destruct H0.
  2: { apply (gfp_bchain R). apply diverges_divpres. now apply diverges_bind. }
  apply simF_equiv. induction H0.
  constructor. intros ??.
  apply trans_bind_inv in H4 as [(? & ? & ? & ?)|(? & ? & ?)].
  - subs. apply H3 in H5 as ?. apply dtau_div. apply H6.
    { intros. apply H2. red in H6 |- *. rewrite str_unfold_l, dotplsx. right.
      rewrite <- dotA. esplit; eauto.
    }
  - specialize (H1 x). apply simF_equiv in H1. revert s' H5.
    assert (divpresF (`R false) (k x) (CTree.bind t' k')).
    2: { apply H5. }
    remember (k x) as kx. assert (KX: (lts.(trans) tau)^* (k x) kx). { subst. now rewrite <- str_refl. } clear Heqkx.
    remember (k' x) as k'x.
    revert k k' x KX Heqk'x H3 H4. induction H1; intros; subst.
    constructor. intros ??.
    apply H1 in H5 as ?. destruct H6.
    + eapply dtau_plus. 2: { apply DIV. }
      specialize (H2 x). lapply H2.
      2: { now apply trans_dtrans. }
      clear H2. intro. eapply tauplus_bind_r; eauto.
      rewrite <- itr_ext. apply TR.
    + destruct DIV.
      eapply dtau_div. destruct DIV.
      eapply H7; eauto.
      rewrite str_unfold_r. right. esplit; eauto.
Qed.

(* requires the excluded middle *)
Lemma divpres_upto_bind {E B X Y} freeze lock : forall
  (R : Chain (simF (lts := lts) freeze lock SimOpt.delay))
  (t t' : ctree E B X) (k k' : X -> ctree E B Y),
  (sim (lts := lts) SimOpt.freeze_div lock SimOpt.delay true t t') ->
  (forall x, `R false (k x) (k' x)) ->
  `R false (CTree.bind t k) (CTree.bind t' k').
Proof.
  intros. eapply divpres_upto_bind'; auto.
  eapply divpres_case; eauto. apply sim_f_t; eauto.
  intros. red in H1 |- *.
  destruct H1. eapply sim_inv_taustar_l in H; eauto.
  apply sim_fp in H. apply H in H2 as [].
  cbn in OBS. subst.
  red in TR. destruct TR. esplit; eauto.
  apply trans_val_inv in H3 as ?. now subs.
Qed.

Lemma is_stuck_bind_inv {E B X Y} : forall (t : ctree E B X) (k : X -> ctree E B Y),
  is_stuck (lts := lts) (CTree.bind t k) ->
  is_stuck (lts := lts) t \/ forall l t', lts.(trans) l t t' -> exists r : X, l = obs (oval r) /\ t' ≅ Stuck.
Proof.
  intros.
  destruct (Classical_Prop.classic (extrans (lts := lts) t)); auto.
  right. intros.
  destruct l.
  2: {
    apply trans_bind_l with (k := k) in H1. 2: apply is_val_τ.
    exfalso. apply H. eexists; apply H1.
  }
  destruct s.
  1: {
    apply trans_bind_l with (k := k) in H1. 2: apply is_val_obs.
    exfalso. apply H. eexists; apply H1.
  }
  apply trans_val_invT in H1 as ?. subst.
  exists x. split; auto.
  now apply trans_val_inv in H1.
Qed.

Lemma upto_bind E B X Y freeze lock delay (TMP : freeze <> SimOpt.freeze_div \/ delay = SimOpt.delay) : forall
  (R : Chain (simF (lts := lts) freeze lock delay))
  (t t' : ctree E B X) (k k' : X -> ctree E B Y)
  (Hlock : lock = SimOpt.nolock \/ forall x, extrans (lts := lts) (k' x)),
  (sim (lts := lts) freeze lock delay true t t') ->
  (forall x, `R true (k x) (k' x)) ->
  `R true (CTree.bind t k) (CTree.bind t' k').
Proof.
  intro. apply tower. {
    intros ???????????. apply H; auto.
    intros. now apply H1.
  }
  clear R. intros R **.
  apply simF_equiv. repeat split; intros.
  - (* observable transition *)
    apply trans_bind_inv in H2 as [(? & ? & ? & ?) | (? & ? & ?)].
    + (* transition from t *)
      subs. apply sim_fp in H0. apply H0 in H3 as []. apply dtrans_case in TR as [TR | [-> TR]].
      * eapply ans_obs. eapply trans_bind_l in TR. apply trans_dtrans. apply TR. cbn in OBS. subst. apply H2.
        apply itr_ext_hrel.
        apply H; auto. apply itr_sim; auto. typeclasses eauto. intros. step. apply H1. apply OBS.
      * eapply ans_obs; auto. instantiate (1 := (CTree.bind t'0 k')).
        { apply dtrans_bind_l; auto. cbn in OBS. subst. now rewrite str_itr' in TR. }
        apply itr_ext_hrel. apply H; auto. intros. apply itr_sim, SIM. typeclasses eauto.
        intros. step. apply H1.
    + (* transition from k *)
      apply sim_fp in H0.
      eapply ObsAnswer_bind_r.
      * lapply (proj1 H0 (oval x) Stuck). 2: { apply H2. }
        intros. eapply ObsAnswer_mon; eauto. cbn. auto.
      * specialize (H1 x). apply simF_equiv in H1. apply (proj1 H1 o s'). apply H3.
  - (* tau transition *)
    apply trans_bind_inv in H2 as [(? & ? & ? & ?) | (? & ? & ?)].
    + (* transition from t *)
      subs. apply sim_fp in H0. apply H0 in H3 as [].
      * eapply tau_exact. eapply trans_bind_l in TR. apply TR. apply is_val_τ.
        apply H; auto. intros. step. apply H1.
      * apply tau_freeze; auto.
        apply H; auto. intros. step. apply H1.
      * apply tau_div; auto. (* TODO simF_step_t *)
        apply H; auto. intros. step. apply H1.
        subst. destruct TMP, delay; try easy.
        eapply divpres_upto_bind; eauto.
        intros. now apply simF_f_t.
      * eapply tau_delay. auto. instantiate (1 := (CTree.bind t'0 k')).
        { apply tauplus_bind_l; auto. }
        apply H; auto. intros. step. apply H1.
    + (* transition from k *)
      apply sim_fp in H0.
      eapply TauAnswer_bind_r. auto.
      * lapply (proj1 H0 (oval x) Stuck). 2: { apply H2. }
        intros. eapply ObsAnswer_mon; eauto. cbn. auto.
      * specialize (H1 x). apply simF_equiv in H1. apply (proj1 (proj2 H1) s'). apply H3.
  - red. destruct Hlock; auto.
    apply sim_fp in H0 as ?. destruct H3 as (_ & _ & []); auto.
    right. intro. red.
    apply is_stuck_bind_inv in H4 as [].
    + apply H3 in H4. destruct delay.
      * red in H4. destruct H4.
        { left. Fail apply is_stuck_bind. admit. }
        destruct H4 as (_ & ? & ? & ?).
        right. split; auto.
        eapply transs_bind_l with (k := k') in H4.
        exists (CTree.bind x k'). split; auto.
        Fail apply is_stuck_bind. admit.
      * destruct H4; try easy.
        left. Fail apply is_stuck_bind. admit.
    + admit.
    (* if t stuck then t' can be stuck so bind t' k' too OK.
      if t pure, it means for all (k x) reachable (k x) is stuck,
      so k' x can be stuck (one is enough) so bind t' k' is stuck.
      I may need the excluded middle? *)
Admitted.
