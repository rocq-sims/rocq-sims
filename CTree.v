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
From OptSim Require Import Utils LTS OptSim.

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
  St := @SS E B X;
  LTS.trans := fun l => {| hrel_of := Trans.trans (clabel l) |};
  (*epsilon := {| hrel_of := fun _ _ => False |};*)
  Robs := eq; (* FIXME heterogeneous relations *)
  ub_state := fun _ => False
|}.

#[export] Instance Chain_simF_equ E B X freeze lock delay b : forall (R : Chain (simF (lts := lts) freeze lock delay)),
  Proper (@equ E B X X eq ==> equ eq ==> impl) (`R b).
Proof.
  intros. cbn. intros.
  eapply (Chain_simF_eq'' (lts := lts)); eauto.
Qed.

Lemma ObsAnswer_bind_r : forall E B X Y delay R (s' : St (@lts E B Y)) (t : St (@lts E B X)) (k : X -> ctree E B Y) x o,
  ObsAnswer (lts := lts) delay (fun _ _ => True) Stuck t (oval x) ->
  ObsAnswer delay R s' (k x) o ->
  ObsAnswer delay R s' (CTree.bind t k) o.
Proof.
  intros. destruct H.
  - cbn in OBS. subst.
    destruct H0.
    + eapply ans_obs; try eassumption. eapply trans_bind_r.
      apply trans_val_inv in TR as ?. rewrite H in TR. apply TR.
      apply TR0.
Admitted.

Lemma epsilon_correct : forall E B X (t u : ctree E B X),
  Epsilon.epsilon t u ->
  OptSim.epsilon (lts := lts) t u.
Proof.
  red. intros.
  eapply epsilon_trans; eauto.
Qed.

Lemma TauAnswer_bind_r : forall E B X Y freeze lock delay (R : Chain (simF freeze lock delay))
  (s' : St (@lts E B Y)) (t : St (@lts E B X)) (k : X -> ctree E B Y) x,
  ObsAnswer (lts := lts) delay (fun _ _ => True) Stuck t (oval x) ->
  TauAnswer freeze delay (`R true) (`R false) s' (k x) ->
  TauAnswer freeze delay (`R true) (`R false) s' (CTree.bind t k).
Proof.
  intros. destruct H.
  - cbn in OBS. subst.
    destruct H0.
    + eapply tau_exact; try eassumption. eapply trans_bind_r.
      apply trans_val_inv in TR as ?. rewrite H in TR. apply TR.
      apply TR0.
    + apply tau_freeze; auto.
      eapply upto_epsilon_r. admit. 2: apply SIM0.
      apply epsilon_correct. eapply epsilon_bind_ret.
      now apply trans_val_epsilon in TR as [].
    + apply tau_div'; auto. intro.
      eapply upto_epsilon_r. admit. 2: destruct b; eauto.
      apply epsilon_correct. eapply epsilon_bind_ret.
      now apply trans_val_epsilon in TR as [].
    + eapply tau_delay; try eassumption. admit.
  - admit.
Admitted.

Lemma upto_bind E B X Y freeze lock delay : forall
  (R : Chain (simF (lts := lts) freeze lock delay))
  b (t t' : ctree E B X) (k k' : X -> ctree E B Y),
  sim (lts := lts) freeze lock delay b t t' ->
  (forall x, `R b (k x) (k' x)) ->
  `R b (CTree.bind t k) (CTree.bind t' k').
Proof.
  intro. apply tower. {
    intros ???????????. apply H; auto.
    intros. now apply H1.
  }
  clear R. intros R **. destruct b.
  2: { admit. }
  apply simF_equiv. repeat split; intros.
  - (* observable transition *)
    apply trans_bind_inv in H2 as [(? & ? & ? & ?) | (? & ? & ?)].
    + (* transition from t *)
      subs. apply sim_fp in H0. apply H0 in H3 as [].
      * eapply ans_obs. eapply trans_bind_l in TR. apply TR. admit.
        apply itr_ext_hrel.
        apply H; auto. apply itr_sim; auto. typeclasses eauto. intros. step. apply H1. apply OBS.
      * eapply ans_delay_obs; auto. instantiate (1 := (CTree.bind t'0 k')). admit.
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
      * eapply tau_exact. eapply trans_bind_l in TR. apply TR. admit.
        apply H; auto. intros. step. apply H1.
      * apply tau_freeze; auto.
        apply H; auto. intros. step. apply H1.
      * apply tau_div; auto. (* TODO simF_step_t *)
        apply H; auto. intros. step. apply H1.
        apply H; auto. intros. apply simF_f_t. now subst. apply H1.
      * eapply tau_delay; auto. instantiate (1 := (CTree.bind t'0 k')). admit.
        apply H; auto. intros. step. apply H1.
    + (* transition from k *)
      apply sim_fp in H0.
      eapply TauAnswer_bind_r.
      * lapply (proj1 H0 (oval x) Stuck). 2: { apply H2. }
        intros. eapply ObsAnswer_mon; eauto. cbn. auto.
      * specialize (H1 x). apply simF_equiv in H1. apply (proj1 (proj2 H1) s'). apply H3.
  - admit.
Admitted.
