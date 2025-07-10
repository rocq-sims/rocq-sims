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
From CTree Require Import CTree Eq Eq.Epsilon Eq.IterFacts.
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
  Robs := eq; (* FIXME heterogeneous relations *)
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
      eapply upto_epsilon_r. 3: apply SIM0.
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
  is_stuck (lts := lts) t \/
    (forall l t', lts.(trans) l t t' -> t' ≅ Stuck /\ exists r : X, l = obs (oval r)) /\ (forall r : X, lts.(trans) (obs (oval r)) t Stuck -> is_stuck (lts := lts) (k r)).
Proof.
  intros.
  destruct (Classical_Prop.classic (extrans (lts := lts) t)); auto.
  right. split; intros.
  - destruct l.
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
    split. now apply trans_val_inv in H1.
    exists x. split; auto.
  - intros [].
    apply trans_bind_r with (t := t) in H2; auto. apply H.
    eexists. apply H2.
Qed.

Lemma label_clabel {E} :
  forall l, exists l', l = clabel (E := E) l'.
Proof.
  intros [].
  - now exists tau.
  - now exists (obs (oobs e v)).
  - now exists (obs (oval v)).
Qed.

Lemma is_stuck_ctree {E B X} : forall (t : ctree E B X),
  is_stuck (lts := lts) t <->
  Trans.is_stuck t.
Proof.
  unfold is_stuck, Trans.is_stuck. split; intro.
  - intros. intro. apply H.
    destruct (label_clabel l) as [? ->].
    econstructor. apply H0.
  - intros []. eapply H. apply H0.
Qed.

Lemma upto_bind E B X Y freeze lock delay (TMP : freeze <> SimOpt.freeze_div \/ delay = SimOpt.delay) : forall
  (R : Chain (simF (lts := lts) freeze lock delay))
  (t t' : ctree E B X) (k k' : X -> ctree E B Y)
  (Hlock : lock = SimOpt.nolock \/ forall x, extrans (lts := lts) (k x) /\ extrans (lts := lts) (k' x)),
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
      eapply TauAnswer_bind_r.
      * destruct Hlock; auto.
        right. intro. apply H4.
      * lapply (proj1 H0 (oval x) Stuck). 2: { apply H2. }
        intros. eapply ObsAnswer_mon; eauto. cbn. auto.
      * specialize (H1 x). apply simF_equiv in H1. apply (proj1 (proj2 H1) s'). apply H3.
  - (* deadlock preservation *)
    red. destruct Hlock; auto.
    apply sim_fp in H0 as ?. destruct H3 as (_ & _ & []); auto.
    destruct lock; auto.
    right. intro. red.
    apply is_stuck_bind_inv in H4 as [].
    + apply H3 in H4. destruct delay.
      * red in H4. destruct H4.
        { left. now apply is_stuck_ctree, is_stuck_bind, is_stuck_ctree. }
        destruct H4 as (_ & ? & ? & ?).
        right. split; auto.
        eapply transs_bind_l with (k := k') in H4.
        exists (CTree.bind x k'). split; auto.
        now apply is_stuck_ctree, is_stuck_bind, is_stuck_ctree.
      * destruct H4; try easy.
        left. now apply is_stuck_ctree, is_stuck_bind, is_stuck_ctree.
    + destruct (Classical_Prop.classic (is_stuck (lts := lts) t)). (* destruct this *before* *)
      * apply sim_fp in H0 as (_ & _ & ?). destruct H0; try easy. apply H0 in H5.
        destruct H5 as [| (-> & ? & ? & ?)].
        { left. now apply is_stuck_ctree, is_stuck_bind, is_stuck_ctree. }
        right. split; auto.
        apply transs_bind_l with (k := k') in H5.
        exists (CTree.bind x k'). split; auto.
        now apply is_stuck_ctree, is_stuck_bind, is_stuck_ctree.
      * apply Classical_Prop.NNPP in H5.
        destruct H5.
        apply H4 in H5 as ?. destruct H6 as (? & ? & ?). subst. subs.
        apply sim_fp in H0. apply H4 in H5 as ?. exfalso. apply H6, H2.
Qed.

Section extrans.

Context {E B : Type -> Type}.
Context {X : Type}.

Lemma extrans_vis :
  forall Y e (k : Y -> ctree E B X) (y : Y),
  extrans (lts := lts) (Vis e k).
Proof.
  intros. eapply trans_intro with (l := obs (oobs e y)). apply trans_vis.
Qed.

Lemma extrans_step :
  forall (t : ctree E B X),
  extrans (lts := lts) (Step t).
Proof.
  intros. eapply trans_intro with (l := tau). apply trans_step.
Qed.

Lemma extrans_ret :
  forall v,
  extrans (lts := lts) (Ret v : ctree E B X).
Proof.
  intros. eapply trans_intro with (l := obs (oval v)). apply trans_ret.
Qed.

End extrans.

Section ProofSystem.

(* TODO heterogeneous return types *)
Context {E B : Type -> Type}.
Context {X : Type}.
Context (freeze : SimOpt.freeze_opt) (lock : SimOpt.lock_opt) (delay : SimOpt.delay_opt).
Context (R : Chain (simF (lts := @lts E B X) freeze lock delay)).
Context (t u : ctree E B X).
Notation simF := (simF (lts := @lts E B X) freeze lock delay).

Lemma c_stuck :
  is_stuck (lts := lts) t /\ (lock = SimOpt.nolock \/ is_stuck (lts := lts) u) ->
  `R true t u.
Proof.
  intros []. step.
  apply simF_equiv. repeat split; intros; esim.
  red. destruct H0; auto.
  right. intros _.
  now apply is_stuck_can_be_stuck.
Qed.

Lemma c_ret :
  forall v,
  `R true (Ret v) (Ret v).
Proof.
  intros. step. apply simF_equiv. repeat split; intros.
  - cbn in H. destruct o; inv_trans.
    apply val_eq_invT in EQl as ?. subst.
    apply val_eq_inv in EQl as ->.
    econstructor; esim.
    apply trans_dtrans. apply trans_ret.
  - cbn in H. inv_trans.
  - right. intro. exfalso. apply H. apply extrans_ret.
Qed.

Lemma c_br_l :
  forall Y (b : B Y) k (Hstuck : lock = SimOpt.nolock \/ exists y : Y, True),
  (forall x, `R true (k x) u) ->
  `R true (Br b k) u.
Proof.
  intros. eapply upto_epsilon_l with (S' := fun t => exists x, t = k x).
  - destruct Hstuck as [|[]]; auto.
    right. exists (k x). split; eauto.
    apply epsilon_correct. eapply epsilon_Br. reflexivity.
  - intros. cbn in H0. inv_trans.
    eauto.
  - intros. destruct H0. subst. eauto.
Qed.

Lemma c_br_r :
  forall Y (b : B Y) k x (Hstuck : lock = SimOpt.nolock \/ extrans (k x) \/ (freeze = SimOpt.nofreeze /\ extrans (lts := lts) t)),
  `R true t (k x) ->
  `R true t (Br b k).
Proof.
  intros. eapply upto_epsilon_r.
  3: apply H.
  - tauto.
  - apply epsilon_correct. now eapply epsilon_Br.
Qed.

Lemma c_step_l (Hfreeze : freeze = SimOpt.freeze) :
  `R true t u ->
  simF `R true (Step t) u.
Proof.
  intros. apply simF_equiv. repeat split; intros.
  - cbn in H0. destruct o; inv_trans.
  - apply tau_freeze; auto.
    cbn in H0. now inv_trans.
  - red. right. intro. exfalso. apply H0. apply extrans_step.
Qed.

Lemma c_step_l' (Hfreeze : freeze = SimOpt.freeze_div) :
  `R true t u ->
  `R true (Step t) u.
Proof.
  intros. subst. eapply upto_tau_l.
  - red. intros. cbn in H0. apply trans_step_inv in H0 as [_ ?].
    now destruct l as [[] |].
  - right. apply extrans_step.
  - intros. cbn in H0. inv_trans. apply H.
Qed.

Lemma c_step_l'' (Hfreeze : freeze = SimOpt.freeze_div) :
  `R true t u ->
  divpres (lts := lts) t u ->
  simF `R true (Step t) u.
Proof.
  intros. subst. apply simF_equiv. repeat split; intros.
  - cbn in H1. inv_trans. now destruct o.
  - cbn in H1. inv_trans. apply tau_div; auto.
    apply (gfp_chain R). now apply sim_f_divpres.
  - right. intro. exfalso. apply H1. apply extrans_step.
Qed.

Lemma c_step_r (Hdelay : delay = SimOpt.delay) :
  `R true t u ->
  `R true t (Step u).
Proof.
  intros. eapply upto_tau_r. auto.
  rewrite <- str_ext. apply trans_step.
  apply H.
Qed.

Lemma c_step :
  `R true t u ->
  simF `R true (Step t) (Step u).
Proof.
  intros. apply simF_equiv. repeat split; intros.
  - cbn in H0. destruct o; inv_trans.
  - cbn in H0. inv_trans. eapply tau_exact; eauto. cbn. etrans.
  - red. right. intro. exfalso. apply H0. apply extrans_step.
Qed.

Lemma c_vis_l :
  forall Y e (k : Y -> ctree E B X)
    (Hdelay : delay = SimOpt.delay) (Hstuck : lock = SimOpt.nolock \/ exists y : Y, (True : Prop)),
  (forall x, exists k', (trans (lts := lts) tau)^* u (Vis e k') /\ `R true (k x) (k' x)) ->
  simF `R true (Vis e k) u.
Proof.
  intros. apply simF_equiv. repeat split; intros.
  - cbn in H0. destruct o; inv_trans. subst.
    destruct (H x0) as (? & ? & ?).
    econstructor. 3: reflexivity.
    + red. esplit. apply H0. apply trans_vis.
    + now apply itr_ext_hrel.
  - cbn in H0. inv_trans.
  - red. destruct Hstuck as [|[]]; auto.
    right. intro. exfalso. apply H1. now apply extrans_vis.
Qed.

Lemma c_vis :
  forall Y e (k k' : Y -> ctree E B X),
  (forall x, `R true (k x) (k' x)) ->
  simF `R true (Vis e k) (Vis e k').
Proof.
  intros. apply simF_equiv. repeat split; intros.
  - cbn in H0. inv_trans. destruct o; try easy.
    apply obs_eq_invT in EQl as ?. subst.
    apply obs_eq_inv in EQl as [-> ->].
    econstructor; eauto.
    + apply trans_dtrans. apply trans_vis.
    + now apply itr_ext_hrel.
  - cbn in H0. inv_trans.
  - right. intro. left. intro.
    destruct H1. cbn in H1. inv_trans.
    apply H0. now apply extrans_vis.
Qed.

End ProofSystem.

Theorem upto_iterS :
  forall {E B X Y} freeze lock delay (TMP : freeze <> SimOpt.freeze_div \/ delay = SimOpt.delay) (R : Chain (simF (lts := lts) freeze lock delay)),
  Proper (pwr (sim (lts := @lts E B (X + Y)) freeze lock delay true) ==> eq ==> `R true) CTree.iterS.
Proof.
  cbn. intros ?????????. apply tower. {
    intros ??????????. apply H; auto.
  }
  clear R. intros R **. subst.
  rewrite !unfold_iterS.
  apply upto_bind; auto.
  - right. intros [].
    + split; apply extrans_step.
    + split; apply extrans_ret.
  - intros [].
    + apply c_step. apply H; auto.
    + apply c_ret.
Qed.
