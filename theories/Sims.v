(* SPDX-FileCopyrightText: 2025 rocq-sims authors *)
(* SPDX-License-Identifier: LGPL-3.0-or-later *)

From Coq Require Import Program.Equality.
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
From Sims Require Import Utils LTS Divergence.

Import CoindNotations.


Section WithLTS.

Context {lts : LTS}.
Notation Observable := lts.(Observable).
Notation St := lts.(St).
Notation trans := lts.(trans).
Notation Robs := lts.(Robs).
Notation label := (@label Observable).

Section SimDef.

Context (freeze : SimOpt.freeze_opt) (lock : SimOpt.lock_opt) (delay : SimOpt.delay_opt).

Notation can_be_stuck := (@can_be_stuck lts delay).
Notation dtrans := (@dtrans lts delay).

(* Simulation game for observable transitions *)

Variant ObsAnswer (R : relation St) s' t o : Prop :=
| ans_obs o' t' (TR : dtrans (obs o') t t') (SIM : R s' t') (OBS : Robs o o') : ObsAnswer R s' t o.

Hint Constructors ObsAnswer : sims.

#[export] Instance ObsAnswer_eq : forall R,
  Proper (St.(Eq) ==> St.(Eq) ==> impl) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> eq ==> impl) (ObsAnswer R).
Proof.
  cbn. intros. subst.
  destruct H3; rewrite ?H0, ?H1 in *; eauto with sims.
Qed.

#[export] Instance ObsAnswer_eq' R :
  Proper (Eq St ==> Eq St ==> impl) R ->
  Proper (Eq St ==> Eq St ==> eq ==> iff) (ObsAnswer R).
Proof.
  intro. cbn. intros. subst.
  split; intro.
  - now rewrite H0, H1 in H2.
  - now rewrite H0, H1.
Qed.

#[export] Instance ObsAnswer_mon : Proper (leq ==> eq ==> eq ==> eq ==> impl) ObsAnswer.
Proof.
  cbn. intros. subst. destruct H3; esim.
Qed.

(* Simulation game for tau transitions *)

Variant TauAnswer (R Rdiv : relation St) s' t : Prop :=
| tau_exact t' (TR : trans tau t t') (SIM : R s' t')
| tau_freeze (_ : freeze = SimOpt.freeze) (SIM : R s' t)
| tau_div (_ : freeze = SimOpt.freeze_div) (SIM : R s' t) (DIV : Rdiv s' t)
| tau_delay t' (_ : delay = SimOpt.delay) (TR : (trans tau)^+ t t') (SIM : R s' t')
.
Hint Constructors TauAnswer : sims.

#[export] Instance : forall R Rdiv,
  Proper (St.(Eq) ==> St.(Eq) ==> impl) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> impl) Rdiv ->
  Proper (St.(Eq) ==> St.(Eq) ==> impl) (TauAnswer R Rdiv).
Proof.
  intros. cbn. intros.
  destruct H3; rewrite ?H1, ?H2 in *; eauto with sims.
Qed.

Lemma tau_weak :
  freeze = SimOpt.freeze ->
  delay = SimOpt.delay ->
  forall R Rdiv s' t t',
  Proper (St.(Eq) ==> St.(Eq) ==> iff) R ->
  (trans tau)^* t t' -> R s' t' -> TauAnswer R Rdiv s' t.
Proof.
  intros -> -> * ? TR SIM.
  rewrite str_itr in TR. destruct TR as [TR | TR].
  - cbn in TR. apply tau_freeze; auto. now rewrite TR.
  - eapply tau_delay; eauto.
Qed.

Lemma tau_weak_div :
  freeze = SimOpt.freeze_div ->
  delay = SimOpt.delay ->
  forall R Rdiv s' t t',
  Proper (St.(Eq) ==> St.(Eq) ==> impl) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> impl) Rdiv ->
  (trans tau)^* t t' -> R s' t' -> Rdiv s' t' -> TauAnswer R Rdiv s' t.
Proof.
  intros -> -> * ?? TR SIM DIV.
  rewrite str_itr in TR. destruct TR as [TR | TR].
  - cbn in TR. apply tau_div; auto; now rewrite TR.
  - eapply tau_delay; eauto.
Qed.

Definition RL l l' :=
  match l, l' with
  | tau, tau => True
  | obs o, obs o' => Robs o o'
  | _, _ => False
  end.

Definition lockpres (s t : St) :=
  (lock = SimOpt.nolock \/ (is_stuck s -> can_be_stuck t)).
Hint Unfold lockpres : sims.

Definition simGame (R : bool -> hrel St St) s t :=
  (forall o s', trans (obs o) s s' -> ObsAnswer ((R true)^+) s' t o) /\
  (forall s', trans tau s s' -> TauAnswer (R true) (R false) s' t) /\
  lockpres s t.

Variant simF_ R : bool -> hrel St St :=
| simF_game s t : simGame R s t -> simF_ R true s t
(*| sim_ub*)
| simF_divpres s t : divpresF (R false) s t -> simF_ R false s t.

Program Definition simF :
  mon (bool -> hrel St St) :=
{| body R b s t :=
  simF_ R b s t
|}.
Next Obligation.
  destruct H0; constructor; repeat split; intros.
  - apply H0 in H1. eapply ObsAnswer_mon. eapply itr_leq. cbn. apply H.
    all: esim.
  - apply H0 in H1 as []; esim.
  - now apply H0.
  - eapply (Hbody divpresF). 2: { apply H0. } cbn. intros. now apply H.
Qed.

Lemma tau_div' : forall (R : Chain simF) s' t,
  freeze = SimOpt.freeze_div ->
  (forall b, `R b s' t) ->
  TauAnswer (`R true) (`R false) s' t.
Proof.
  intros. apply tau_div; auto.
Qed.

#[export] Instance lockpres_eq :
  Proper (Eq St ==> Eq St ==> impl) lockpres.
Proof.
  cbn. intros. red in H1 |- *.
  now rewrite <- H, <- H0.
Qed.

Lemma simF_eq_ R :
  (forall b, Proper (Eq St ==> Eq St ==> impl) (R b)) ->
  forall b, Proper (Eq St ==> Eq St ==> impl) (simF R b).
Proof.
  intros. cbn. intros. subst. destruct H2; constructor.
  - destruct H2 as (? & ? & ?).
    repeat split; intros; rewrite <- ?H0, <- ?H1 in * |- *; auto.
  - now rewrite H0, H1 in H2.
Qed.

#[export] Instance simF_eq R :
  Proper (eq ==> Eq St ==> Eq St ==> impl) R ->
  Proper (eq ==> Eq St ==> Eq St ==> impl) (simF R).
Proof.
  intros. cbn. intros. subst.
  eapply simF_eq_; eauto. intro. now apply H.
Qed.

#[export] Instance Chain_simF_eq : forall (R : Chain simF),
  Proper (eq ==> Eq St ==> Eq St ==> impl) ` R.
Proof.
  intro. apply tower. {
    intros ? INC ?? <- ??????. intros ???.
    - eapply INC. assumption. reflexivity.
      now rewrite <- H. now rewrite <- H0.
      now apply H1.
  }
  intros. cbn. intros; subst.
  now rewrite H1, H2 in H3.
Qed.

(* explicit instance needed for ternary Proper *)
#[export] Instance Chain_simF_eq' : forall (R : Chain simF),
  Proper (eq ==> Eq St ==> Eq St ==> iff) ` R.
Proof.
  intros. split; apply Chain_simF_eq; auto; now symmetry.
Qed.

#[export] Instance Chain_simF_eq'' : forall (R : Chain simF) b,
  Proper (Eq St ==> Eq St ==> impl) (`R b).
Proof.
  cbn. intros. eapply Chain_simF_eq; eauto.
Qed.

Definition sim : bool -> hrel St St := gfp simF.

Lemma simF_false : forall R s t,
  simF R false s t ->
  divpresF (R false) s t.
Proof.
  intros. now inversion H.
Qed.
Hint Resolve simF_false : sims.

Lemma simF_true : forall R s t,
  simF R true s t ->
  simGame R s t.
Proof.
  intros. now inversion H.
Qed.
Hint Resolve simF_true : sims.

Lemma simF_equiv : forall R s t,
  (simF R false s t <->
  divpresF (R false) s t) /\
  (simF R true s t <->
  simGame R s t).
Proof.
  intros; split; split; intro; try now inversion H; try now constructor.
Qed.

Lemma sim_fp : forall s t,
  (sim false s t <->
  divpresF (sim false) s t) /\
  (sim true s t <->
  simGame sim s t).
Proof.
  intros; split; split; intro.
  - apply (gfp_fp simF) in H. now inversion H.
  - apply (gfp_fp simF). now constructor.
  - apply (gfp_fp simF) in H. now inversion H.
  - apply (gfp_fp simF). now constructor.
Qed.

Lemma sim_tau_weak :
  forall s s' t R,
  simF R true s t ->
  trans tau s s' ->
  exists t', (trans tau)^* t t' /\ R true s' t'.
Proof.
  intros. inversion H; subst. apply H1 in H0 as []; auto.
  - exists t'. split; auto. now rewrite <- str_ext.
  - exists t. split; auto. now rewrite <- str_refl.
  - exists t. split; auto. now rewrite <- str_refl.
  - exists t'. split; auto. now rewrite <- str_itr'.
Qed.

(* Alternative definition, without built-in transitivity for observable events *)

Variant SimAnswer (R Rdiv : relation St) s' t l : Prop :=
| ans_exact l' t' (TR : trans l' t t') (SIM : R s' t') (LBL : RL l l')
| ans_freeze (_ : freeze = SimOpt.freeze) (SIM : R s' t) (LBL : l = tau)
| ans_div (_ : freeze = SimOpt.freeze_div) (SIM : R s' t) (DIV : Rdiv s' t) (LBL : l = tau)
| ans_delay l' t' (_ : delay = SimOpt.delay) (TR : ((trans tau)^+ ⋅ trans l') t t') (SIM : R s' t') (LBL : RL l l')
.
Hint Constructors SimAnswer : sims.

#[export] Instance : forall R Rind,
  Proper (St.(Eq) ==> St.(Eq) ==> iff) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> iff) Rind ->
  Proper (St.(Eq) ==> St.(Eq) ==> eq ==> flip impl) (SimAnswer R Rind).
Proof.
  intros. cbn. intros. subst.
  destruct H4; rewrite <- ?H1, <- ?H2 in *; eauto with sims.
Qed.

Definition sim_alt R s t :=
  (forall l s', trans l s s' -> SimAnswer (R true) (R false) s' t l) /\
  lockpres s t.

Lemma sim_alt_equiv : forall R s t, sim_alt R s t -> simF R true s t.
Proof.
  intros. destruct H.
  apply simF_equiv. repeat split; intros; auto.
  - apply H in H1 as []; try discriminate.
    + destruct l'; try easy. econstructor; esim.
    + destruct l'; try easy. econstructor; esim.
      red. rewrite H1. now rewrite <- str_itr'.
  - apply H in H1 as []; esim; try (destruct l'; try easy); esim.
    eapply tau_delay; eauto. rewrite itr_unfold_r. now right.
Qed.

(* Divergence preservation *)

Lemma chain_div : forall (R : Chain simF) s t,
  diverges t ->
  simF `R false s t.
Proof.
  intro. apply tower. {
    intros ???????. apply H; auto.
  }
  clear R. intros R **. constructor.
  constructor. intros ??.
  apply (gfp_fp divergesF) in H0 as (? & ? & ?).
  eapply dtau_match.
  apply H0. auto.
Qed.

Lemma chain_nodiv : forall (R : Chain simF) s t,
  nodiv s ->
  simF `R false s t.
Proof.
  intro. apply tower. {
    intros ???????. apply H; auto.
  }
  clear R. intros R **.
  cbn. constructor.
  induction H0.
  constructor. intros ??.
  apply dtau_div. apply H1. apply H2.
Qed.

Lemma divpresF_tau_r : forall (R : Chain simF) s t t',
  `R false s t' ->
  (trans tau)^* t t' ->
  `R false s t.
Proof.
  intro. apply tower. {
    intros ?????????. eapply H; eauto.
  }
  clear R. intros R **.
  apply simF_equiv in H0. induction H0.
  do 2 constructor. intros ??.
  apply H0 in H2 as [].
  - assert ((trans tau)^+ t t'). { rewrite itr_str_r. esplit; eassumption. }
    rewrite itr_str_l in H2. destruct H2. esim.
  - apply dtau_div. apply simF_equiv. now apply DIV.
Qed.

Lemma dtau_plus : forall (R : Chain simF) Rind s' t t',
  (trans tau)^+ t t' ->
  `R false s' t' ->
  DTauAnswer (` R false) Rind s' t.
Proof.
  intros.
  rewrite itr_str_l in H. destruct H.
  eapply dtau_match. apply H.
  eapply divpresF_tau_r; eauto.
Qed.
Hint Resolve dtau_plus : sims.

Lemma divpres_impl : forall s t,
  sim false s t ->
  diverges s -> diverges t.
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp simF) in H. apply simF_equiv in H.
  induction H. apply (gfp_fp divergesF) in H0 as (? & ? & ?).
  apply H in H0 as [].
  - exists t'. eauto.
  - now apply DIV.
Qed.

Lemma diverges_divpres :
  forall s t, diverges t -> sim false s t.
Proof.
  red. coinduction R CH.
  intros. do 2 constructor. intros ??.
  apply (gfp_fp divergesF) in H as (? & ? & ?).
  eleft; eauto.
Qed.

Lemma sim_f_divpres :
  forall s t, divpres s t <-> sim false s t.
Proof.
  split; revert s t; red; coinduction R CH; intros.
  - apply (gfp_fp divpresF) in H.
    induction H. apply simF_equiv. constructor.
    intros ??. apply H in H0 as []; esim.
    apply dtau_div. eapply (Hbody divpresF).
    cbn. apply CH. apply DIV.
  - apply (gfp_fp simF) in H.
    apply simF_equiv in H. induction H. constructor.
    intros ??. apply H in H0 as []; esim.
    apply dtau_div. eapply (Hbody divpresF).
    cbn. apply CH. apply DIV.
Qed.


(* Divergence-sensitive simulation implies divergence preservation *)

Lemma simF_f_t : forall (Hfreeze : freeze <> SimOpt.freeze) (R : Chain simF) s t,
  simF `R true s t ->
  `R false s t.
Proof.
  intros ?????. apply simF_equiv in H. revert s t H. apply tower. {
    intros ???????. eapply H; eauto.
    apply simF_equiv. eapply (Hbody simF).
    apply leq_infx. apply H1. apply simF_equiv, H0.
  }
  clear R. intros R **. do 2 constructor.
  intros ??. apply H0 in H1 as []; esim.
  apply dtau_div. eapply simF_equiv. apply DIV.
Qed.

Lemma simF_f_divpres : forall (R : Chain simF) s t,
  divpres s t ->
  `R false s t.
Proof.
  intros. now apply (gfp_chain R), sim_f_divpres.
Qed.

Lemma sim_f_t : forall s t (Hfreeze : freeze = SimOpt.freeze_div),
  sim true s t ->
  sim false s t.
Proof.
  intros. apply (gfp_fp simF) in H. red.
  revert s t H. apply gfp_prop.
  intros. apply simF_f_t; auto.
  now rewrite Hfreeze.
Qed.


(* Up-to principles *)

Section SimUpTo.

Context (R : Chain simF).

#[export] Instance upto_refl `{Reflexive _ Robs} b :
  Reflexive (`R b).
Proof.
  apply tower.
  - firstorder.
  - destruct b; constructor; esim. repeat split; esim.
Qed.

Lemma lockpres_taustar_r (Hdelay : delay = SimOpt.delay) :
  forall s t u,
  lockpres s u ->
  (trans tau)^* t u ->
  lockpres s t.
Proof.
  red. intros.
  destruct lock eqn:?; auto. right. intro.
  destruct H; try now rewrite Heql in *.
  apply H in H1.
  eapply can_be_stuck_taustar; eauto.
Qed.

Theorem upto_tau_r :
  forall s t t'
    (Hdelay : delay = SimOpt.delay),
  (trans tau)^* t t' ->
  `R true s t' ->
  `R true s t.
Proof.
  apply tower. {
    intros ? INC s t t' ?????. red.
    eapply INC; auto.
    apply H.
    apply leq_infx in H1.
    now apply H1.
  }
  intros. constructor. apply simF_equiv in H1.
  repeat split; intros; subst.
  + (* observable event *)
    apply H1 in H2 as [].
    esplit; eauto.
    unfold dtrans in *. rewrite Hdelay in *.
    destruct TR. esplit. 2: apply H3.
    rewrite <- str_trans. esplit; eassumption.
  + (* tau *)
    apply H1 in H2 as [].
    * econstructor 4; eauto.
      rewrite itr_str_r. esplit; eauto.
    * eapply tau_weak; eauto with sims. typeclasses eauto.
    * eapply tau_weak_div; eauto with sims; typeclasses eauto.
    * econstructor 4; eauto.
      rewrite itr_str_r, <- str_trans, <- dotA, <- itr_str_r.
      esplit; eauto.
  + (* deadlock *)
    eapply lockpres_taustar_r; eauto. apply H1.
Qed.

(* useless if freeze is set *)
Theorem inv_tau_l :
  forall s s' t
    (Hdelay : delay = SimOpt.delay),
  trans tau s s' ->
  simF `R true s t ->
  `R true s' t.
Proof.
  intros. apply simF_equiv in H0.
  destruct H0 as (_ & ? & ?).
  apply H0 in H as [].
  - eapply upto_tau_r; eauto. now rewrite <- str_ext.
  - apply SIM.
  - apply SIM.
  - eapply upto_tau_r; eauto. rewrite str_itr. now right.
Qed.

End SimUpTo.

Theorem sim_tau_r :
  forall s t t'
    (Hdelay : delay = SimOpt.delay),
  (trans tau)^* t t' ->
  sim true s t' ->
  sim true s t.
Proof.
  unfold sim. intros ???. apply gfp_prop.
  intros. eapply upto_tau_r; eauto.
Qed.

Theorem sim_inv_tau_l :
  forall (Hdelay : delay = SimOpt.delay) s s' t,
  trans tau s s' ->
  sim true s t ->
  sim true s' t.
Proof.
  unfold sim. intros. apply (gfp_fp simF) in H0. revert H0. eapply gfp_prop.
  intros. eapply inv_tau_l; eauto.
Qed.

Theorem sim_inv_taustar_l :
  forall (Hdelay : delay = SimOpt.delay) s s' t,
  (trans tau)^* s s' ->
  sim true s t ->
  sim true s' t.
Proof.
  intros. revert H0.
  eapply srel_str_ind_l' with (i := trans tau) (P := fun s s' => sim true s t -> sim true s' t); auto.
  - cbn. intros ??????. now rewrite H0, H1.
  - intros. rewrite <- H0. apply H1.
  - intros. apply H1. eapply sim_inv_tau_l; eauto.
Qed.

Lemma simF_epsilon_l :
  forall R s S' t (Hstuck : lock = SimOpt.nolock \/ exists s', S' s' /\ epsilon s s'),
  (forall l t, trans l s t -> exists s', S' s' /\ trans l s' t) ->
  (forall s', S' s' -> simF R true s' t) ->
  simF R true s t.
Proof.
  intros. apply simF_equiv. repeat split; intros.
  - apply H in H1 as ?. destruct H2 as (? & ? & ?).
    apply H0 in H2 as ?. apply simF_equiv in H4. apply H4.
    apply H3.
  - apply H in H1 as ?. destruct H2 as (? & ? & ?).
    apply H0 in H2 as ?. apply simF_equiv in H4. apply H4.
    apply H3.
  - destruct Hstuck; esim.
    destruct H1 as (? & ? & ?).
    apply H0, simF_equiv in H1 as (_ & _ & ?).
    red. destruct H1; auto.
    right. intros. apply H1. intros [].
    apply H2 in H4. esim.
Qed.

Lemma upto_epsilon_l :
  forall (R : Chain simF) s S' t (Hstuck : lock = SimOpt.nolock \/ exists s', S' s' /\ epsilon s s'),
  (forall l t, trans l s t -> exists s', S' s' /\ trans l s' t) ->
  (forall s', S' s' -> `R true s' t) ->
  `R true s t.
Proof.
  intro. apply tower. {
    intros ??????????. eapply H; eauto.
    intros. apply leq_infx in H2. apply H2. eauto.
  }
  clear R. intros R **. eapply simF_epsilon_l; eauto.
Qed.

Lemma upto_epsilon_r :
  forall (R : Chain simF) b s t t' (Hstuck : (freeze = SimOpt.nofreeze /\ extrans s) \/ lock = SimOpt.nolock \/ extrans t'),
  epsilon t t' ->
  `R b s t' ->
  `R b s t.
Proof.
  intro. apply tower. {
    intros ???????????. eapply H; eauto.
  }
  clear R. intros R **.
  destruct b. 2: {
    apply simF_equiv in H1. clear Hstuck. induction H1.
    do 2 constructor. intros ??.
    apply H1 in H2 as []; esim.
    destruct DIV. apply dtau_div.
    apply simF_equiv. apply H3; auto.
  }
  apply simF_equiv in H1. apply simF_equiv. repeat split; intros.
  - apply H1 in H2 as []; esim.
    esplit; eauto.
    eapply epsilon_dtrans; eauto.
  - apply H1 in H2 as []; destruct Hstuck as [[-> ?]|];
      try discriminate;
      eauto 6 using epsilon_plus with sims.
  - destruct H1 as (_ & _ & []); esim.
    red. destruct Hstuck as [|[|]]; auto.
    + destruct H2. esim.
    + right. intro. eapply epsilon_can_be_stuck; eauto.
Qed.

Lemma lockpres_sim_r :
  forall s t u, lockpres s t -> sim true t u ->
  lockpres s u.
Proof.
  red. intros.
  destruct lock eqn:?; auto. right. intro.
  destruct H; try now rewrite Heql in *.
  apply sim_fp in H0 as ?.
  destruct H2 as (_ & _ & []); try now rewrite Heql in *.
  apply H in H1 as [|(? & ? & ? & ?)]. now apply H2 in H1.
  eapply sim_inv_taustar_l in H3; eauto.
  apply sim_fp in H3 as (_ & _ & []); try now rewrite Heql in *. auto.
Qed.

Lemma sim_diverges : forall (Hfreeze : freeze = SimOpt.freeze_div) s t,
  sim true s t ->
  diverges s ->
  diverges t.
Proof.
  intros. eapply divpres_impl; eauto. apply sim_f_t; auto.
Qed.

Lemma divpres_trans_l : forall (R : Chain simF) s t u,
  `R false t u ->
  sim false s t ->
  `R false s u.
Proof.
  intros ?. apply tower. {
    intros ?????????. eapply H; eauto.
  }
  clear R. intros R **.
  apply simF_equiv in H0.
  revert s H1. induction H0. rename t into u. rename s into t. intros.
  apply (gfp_fp simF) in H1. apply simF_equiv in H1. induction H1.
  apply simF_equiv. constructor. intros ??.
  apply H1 in H2 as ?. destruct H3.
  - apply H0 in TR. destruct TR.
    + rename t'0 into u'. eapply dtau_match; eauto.
    + apply dtau_div. apply DIV0 in DIV. apply simF_equiv. apply DIV; auto.
  - apply dtau_div. apply simF_equiv. apply DIV; auto.
Qed.

Lemma divpres_case : forall s t,
  sim false s t ->
  nodiv s \/ diverges t.
Proof.
  intros. destruct (Classical.diverges_lem s).
  - apply divpres_impl in H; auto.
  - auto.
Qed.

(* Top-level transitivity *)

#[export] Instance divpres_trans : Transitive (sim false).
Proof.
  cbn. red. coinduction R CH. intros. eapply divpres_trans_l. 2: apply H.
  apply (gfp_bchain R). apply H0.
Qed.

Lemma sim_game_delay_tau : forall s s' t,
  (trans tau)^* s s' ->
  sim true s t ->
  exists t', (trans tau)^* t t' /\ sim true s' t'.
Proof.
  intros * TR SIM.
  revert t SIM. eapply srel_str_ind_l' with (P := fun s s' =>
    forall t : St, sim true s t -> exists t' : St, (trans tau)^* t t' /\ sim true s' t'). 4: apply TR.
  all: clear s s' TR.
  { intros ?????????. setoid_rewrite <- H0. apply H1. now rewrite H. }
  - intros * EQ ? SIM. rewrite EQ in SIM.
    setoid_rewrite <- str_refl. cbn. eauto.
  - intros * TR IH ? SIM.
    eapply sim_tau_weak in TR. 2: { apply (gfp_fp simF) in SIM. apply SIM. }
    destruct TR as (? & ? & ?). apply IH in H0 as (? & ? & ?).
    exists x0. split; auto. rewrite <- str_trans. esplit; eassumption.
Qed.

Lemma TauAnswer_tau_l (Hdelay : delay = SimOpt.delay) : forall s t t',
  trans tau t t' ->
  TauAnswer (sim true) (sim false) s t' ->
  TauAnswer (sim true) (sim false) s t.
Proof.
  intros * TR []; esim.
  - eapply tau_delay; eauto. rewrite <- itr_cons, <- itr_ext.
    esplit; eauto.
  - eapply tau_delay; eauto. rewrite <- itr_cons.
    esplit; eauto.
Qed.

Lemma TauAnswer_taustar_l (Hdelay : delay = SimOpt.delay) : forall s t t',
  (trans tau)^* t t' ->
  TauAnswer (sim true) (sim false) s t' ->
  TauAnswer (sim true) (sim false) s t.
Proof.
  intros * TR ANS. revert s ANS.
  eapply srel_str_ind_l' with (P := fun t t' =>
    forall s : St, TauAnswer (sim true) (sim false) s t' -> TauAnswer (sim true) (sim false) s t).
  4: apply TR. clear t t' TR.
  { intros ?????????. setoid_rewrite <- H. apply H1. now rewrite H0. }
  - intros. now rewrite H.
  - intros. eapply TauAnswer_tau_l; eauto.
Qed.

Lemma sim_game_delay_tauplus (Hdelay : delay = SimOpt.delay) : forall s s' t,
  (trans tau)^+ s s' ->
  sim true s t ->
  TauAnswer (sim true) (sim false) s' t.
Proof.
  intros * TR SIM.
  revert t SIM.
  eapply srel_itr_ind_l' with (P := fun s s' =>
    forall t : St, sim true s t -> TauAnswer (sim true) (sim false) s' t). 4: apply TR.
  all: clear s s' TR.
  { intros ?????????. setoid_rewrite <- H0. apply H1. now rewrite H. }
  - intros * TR ? SIM.
    apply sim_fp in SIM. now apply SIM in TR.
  - intros * TR IH ? SIM.
    apply sim_fp in SIM. apply SIM in TR as []; esim.
    + (* tau_exact *)
      apply IH in SIM0. eapply TauAnswer_tau_l; eauto.
    + (* tau_delay *)
      apply IH in SIM0.
      rewrite str_itr' in TR.
      eapply TauAnswer_taustar_l; eauto.
Qed.

Lemma sim_game_delay_obs : forall s s' t o,
  dtrans (obs o) s s' ->
  sim true s t ->
  exists t' o', dtrans (obs o') t t' /\ (sim true)^+ s' t' /\ Robs o o'.
Proof.
  unfold dtrans. intros. destruct delay eqn:?.
  - destruct H as [s0 TR0 TR].
    eapply sim_game_delay_tau in TR0; eauto.
    destruct TR0 as (t' & TR0 & SIM).
    apply sim_fp in SIM. apply SIM in TR as [].
    exists t'0, o'. split; auto. rewrite <- str_trans, <- dotA. esplit; esim.
  - apply sim_fp in H0. apply H0 in H. destruct H. red in TR.
    rewrite Heqd in TR. eauto.
Qed.

#[export] Instance trans_itr X (R : hrel X X) : Transitive (itr (ops := hrel_monoid_ops) _ R).
Proof.
  red. intros. apply (itr_trans (X := hrel_monoid_ops)).
  esplit; eauto.
Qed.

#[export] Instance sim_trans (OBS : Transitive Robs) : forall b, Transitive (sim b).
Proof.
  intros []. 2: typeclasses eauto.
  cbn. red. coinduction R CH. intros. apply simF_equiv.
  assert (TRANS : Transitive (sim true : hrel St St)^+). { typeclasses eauto. }
  repeat split; intros.
  - eapply ObsAnswer_mon. 2, 3, 4: reflexivity.
    { cbn -[itr]. intros. eapply (itr_leq (X := hrel_monoid_ops)). apply (gfp_chain R). apply H2. }
    apply sim_fp in H. apply H in H1 as [].
    eapply sim_game_delay_obs in TR as (t'' & o'' & TR & SIM' & OBS'); esim.
  - apply sim_fp in H. apply H in H1 as []; esim.
    + (* tau_exact *) apply sim_fp in H0. apply H0 in TR as []; esim.
      apply tau_div; eauto.
      apply (gfp_chain R). etransitivity; eauto. now apply sim_f_t.
    + (* tau_div *) apply tau_div; eauto.
      apply (gfp_chain R). etransitivity; eauto. now apply sim_f_t.
    + (* tau_delay *) apply sim_fp in H0.
      eapply sim_game_delay_tauplus in TR; eauto. 2: { apply sim_fp; eauto. }
      destruct TR; esim.
      apply tau_div; eauto.
      apply (gfp_chain R). etransitivity; eauto. now apply sim_f_t.
  - apply sim_fp in H as ?. destruct H1 as (_ & _ & ?).
    eapply lockpres_sim_r in H1; eauto.
Qed.

Lemma itr_sim : forall b s t, Transitive Robs -> (sim b)^+ s t <-> sim b s t.
Proof.
  split; intro.
  - eapply hrel_itr_ind_l'. 3: apply H0.
    + auto.
    + intros. etransitivity; eauto.
  - now apply itr_ext_hrel.
Qed.

End SimDef.

Hint Constructors ObsAnswer : sims.
Hint Constructors TauAnswer : sims.
Hint Resolve dtau_plus : sims.
Hint Resolve simF_false : sims.
Hint Resolve simF_true : sims.

(* Comparison of the simulation options *)

Lemma simF_nofreeze :
  forall freeze lock delay R b s t,
  simF SimOpt.nofreeze lock delay R b s t ->
  simF freeze lock delay R b s t.
Proof.
  intros. destruct b; apply simF_equiv in H; apply simF_equiv.
  2: apply H.
  repeat split; try apply H.
  intros. now apply H in H0 as []; esim.
Qed.

Lemma sim_nofreeze :
  forall freeze lock delay b s t,
  sim SimOpt.nofreeze lock delay b s t ->
  sim freeze lock delay b s t.
Proof.
  intros. red. eapply (gfp_leq (x := simF _ _ _) (y := simF _ _ _)).
  cbn. apply simF_nofreeze. apply H.
Qed.

Lemma simF_freeze :
  forall freeze lock delay R b s t,
  simF freeze lock delay R b s t ->
  simF SimOpt.freeze lock delay R b s t.
Proof.
  intros. destruct b; apply simF_equiv in H; apply simF_equiv.
  2: apply H.
  repeat split; try apply H.
  intros. now apply H in H0 as []; esim.
Qed.

Lemma sim_freeze :
  forall freeze lock delay b s t,
  sim freeze lock delay b s t ->
  sim SimOpt.freeze lock delay b s t.
Proof.
  intros. red. eapply (gfp_leq (x := simF _ _ _) (y := simF _ _ _)).
  cbn. apply simF_freeze. apply H.
Qed.

Lemma simF_nodelay :
  forall freeze lock delay R b s t,
  simF freeze lock SimOpt.nodelay R b s t ->
  simF freeze lock delay R b s t.
Proof.
  intros. destruct b; apply simF_equiv in H; apply simF_equiv.
  2: apply H.
  repeat split; intros.
  - apply H in H0 as []. esim.
  - now apply H in H0 as []; esim.
  - red. destruct H as (_ & _ & []); auto.
    right. intro. apply H in H0.
    red. now destruct H0 as [|[]]; auto.
Qed.

Lemma sim_nodelay :
  forall freeze lock delay b s t,
  sim freeze lock SimOpt.nodelay b s t ->
  sim freeze lock delay b s t.
Proof.
  intros. red. eapply (gfp_leq (x := simF _ _ _) (y := simF _ _ _)).
  cbn. apply simF_nodelay. apply H.
Qed.

Lemma simF_delay :
  forall freeze lock delay R b s t,
  simF freeze lock delay R b s t ->
  simF freeze lock SimOpt.delay R b s t.
Proof.
  intros. destruct delay; auto. now apply simF_nodelay.
Qed.

Lemma sim_delay :
  forall freeze lock delay b s t,
  sim freeze lock delay b s t ->
  sim freeze lock SimOpt.delay b s t.
Proof.
  intros. red. eapply (gfp_leq (x := simF _ _ _) (y := simF _ _ _)).
  cbn. apply simF_delay. apply H.
Qed.

Lemma simF_nolock :
  forall freeze lock delay R b s t,
  simF freeze lock delay R b s t ->
  simF freeze SimOpt.nolock delay R b s t.
Proof.
  intros. destruct b; apply simF_equiv in H; apply simF_equiv.
  2: apply H.
  repeat split; try apply H. now left.
Qed.

Lemma sim_nolock :
  forall freeze lock delay b s t,
  sim freeze lock delay b s t ->
  sim freeze SimOpt.nolock delay b s t.
Proof.
  intros. red. eapply (gfp_leq (x := simF _ _ _) (y := simF _ _ _)).
  cbn. apply simF_nolock. apply H.
Qed.

Lemma simF_lock :
  forall freeze lock delay R b s t,
  simF freeze SimOpt.lock delay R b s t ->
  simF freeze lock delay R b s t.
Proof.
  intros. destruct lock; auto. eapply simF_nolock; eauto.
Qed.

Lemma sim_lock :
  forall freeze lock delay b s t,
  sim freeze SimOpt.lock delay b s t ->
  sim freeze lock delay b s t.
Proof.
  intros. red. eapply (gfp_leq (x := simF _ _ _) (y := simF _ _ _)).
  cbn. apply simF_lock. apply H.
Qed.

(* Up-to principles with heterogeneous options *)

Theorem simF_step_freeze :
  forall lock delay (R : Chain (simF SimOpt.freeze_div lock delay)) s t,
  (simGame SimOpt.freeze lock delay `R s t) ->
  `R true s t.
Proof.
  intros ???. apply tower. {
    intros ???????. apply H; auto.
    apply simF_equiv in H0. apply simF_equiv.
    eapply (Hbody (simF _  _ _)). apply leq_infx. apply H1.
    apply H0.
  }
  clear R. intros R **.
  intros.
  apply simF_equiv. repeat split; intros.
  - apply H0 in H1 as [].
    eapply ans_obs; eauto.
    eapply (itr_leq (X := hrel_monoid_ops)). apply (b_chain R). assumption.
  - apply H0 in H1 as []; esim.
    + eapply tau_exact; eauto. now apply (b_chain R).
    + apply tau_div; auto. apply (b_chain R). apply SIM.
      apply simF_f_t. easy. apply SIM.
    + discriminate.
    + eapply tau_delay; eauto. apply (b_chain R). apply SIM.
  - apply H0.
Qed.

Corollary upto_tau_l :
  forall lock delay (R : Chain (simF SimOpt.freeze_div lock delay)) s t,
  is_tau_state s ->
  forall (Hstuck : lock = SimOpt.nolock \/ extrans s),
  (forall s', trans tau s s' -> `R true s' t) ->
  `R true s t.
Proof.
  intros ???. intros.
  eapply simF_step_freeze.
  repeat split; intros.
  - now apply H in H1.
  - apply H0 in H1. apply tau_freeze; auto.
  - destruct Hstuck. now left. right. esim.
Qed.

Lemma divpres_nofreeze_r : forall lock delay (R : Chain (simF SimOpt.freeze_div lock delay)) s t u,
  `R false s t ->
  sim SimOpt.nofreeze lock delay true t u ->
  `R false s u.
Proof.
  intros ???. apply tower. {
    intros ?????????. eapply H; eauto.
  }
  clear R. intros R **. apply simF_equiv in H0.
  induction H0. do 2 constructor. intros ??. apply H0 in H2 as [].
  - apply sim_fp in H1. apply H1 in TR as []; now esim.
  - right. apply DIV in H1. apply simF_equiv in H1. apply H1; auto.
Qed.

Lemma ObsAnswer_sim_r :
  forall freeze lock delay (OBS : Transitive Robs)
  (R : Chain (simF freeze lock delay)) s' t t' o,
  ObsAnswer delay (`R true : hrel St St)^+ s' t' o ->
  sim freeze lock delay true t' t ->
  ObsAnswer delay (`R true : hrel St St)^+ s' t o.
Proof.
  intros.
  assert (TRANS : Transitive (`R true)^+). { typeclasses eauto. }
  destruct H. destruct delay.
  - destruct TR as [t'' TR0 TR].
    eapply sim_inv_taustar_l in H0; eauto.
    apply sim_fp in H0. apply H0 in TR.
    eapply ObsAnswer_mon in TR.
    3, 4, 5: reflexivity.
    2: { cbn -[itr]. intros. apply itr_sim, (gfp_chain R) in H; auto. apply H. }
    destruct TR; esim.
  - apply (gfp_bchain R) in H0.
    apply simF_equiv in H0. apply H0 in TR. destruct TR; esim.
Qed.

Theorem upto_trans_r_obs :
  forall freeze lock delay (R : Chain (simF freeze lock delay)) s t t'
    (OBS : Transitive Robs) (Hobs : is_obs_state s),
  `R true s t' ->
  sim freeze lock delay true t' t ->
  `R true s t.
Proof.
  intros ????.
  apply tower. {
    intros ???????????. red.
    eapply H; eauto.
    apply leq_infx in H2. apply H2, H0.
  }
  intros. constructor. apply simF_equiv in H0.
  repeat split; intros; subst.
  - eapply ObsAnswer_sim_r; eauto.
    apply H0 in H2 as []; esim.
  - now apply Hobs in H2.
  - destruct H0 as (_ & _ & ?).
    eapply lockpres_sim_r in H0; eauto.
Qed.

Theorem upto_trans_r :
  forall freeze lock delay (R : Chain (simF freeze lock delay)) s t t'
    (OBS : Transitive Robs),
  `R true s t' ->
  sim (match freeze with SimOpt.freeze_div => SimOpt.nofreeze | _ => freeze end) lock delay true t' t ->
  `R true s t.
Proof.
  intros ????.
  apply tower. {
    intros ??????????. red.
    eapply H; eauto.
    apply leq_infx in H2. apply H2, H0.
  }
  intros. constructor. apply simF_equiv in H0.
  repeat split; intros; subst.
  - eapply ObsAnswer_sim_r; eauto.
    2: { destruct freeze; eauto. now apply sim_nofreeze. }
    apply H0 in H2 as []; esim.
  - apply H0 in H2 as []; auto.
    + (* tau_exact *) apply sim_fp in H1.
      apply H1 in TR as ?. destruct H2; eauto with sims.
      * (* freeze *) destruct freeze; try discriminate.
        apply tau_freeze; auto. eapply H; eauto.
      * (* freeze_div *) destruct freeze; discriminate.
    + (* tau_freeze *) subst freeze.
      eapply tau_freeze; eauto.
    + (* tau_div *) subst freeze.
      eapply tau_div; eauto with sims.
      eapply divpres_nofreeze_r; eauto.
    + (* tau_delay *)
      rewrite itr_str_r in TR. destruct TR as [t'1 TR1 TR2].
      subst.
      eapply sim_inv_taustar_l in H1; eauto.
      apply sim_fp in H1.
      apply H1 in TR2; auto.
      destruct freeze; destruct TR2; try discriminate; eauto with sims.
  - destruct H0 as (_ & _ & ?).
    eapply lockpres_sim_r in H0; eauto.
Qed.

Lemma can_be_stuck_obs_state : forall delay (s : St),
  is_obs_state s ->
  can_be_stuck delay s ->
  is_stuck s.
Proof.
  intros.
  destruct H0; auto.
  destruct H0 as (-> & ? & ? & ?).
  rewrite str_unfold_l in H0. destruct H0.
  - cbn in H0. now rewrite H0.
  - destruct H0. now apply H in H0.
Qed.

Lemma lockpres_obs_state_r : forall lock delay s t,
  is_obs_state t ->
  lockpres lock delay s t ->
  lockpres lock SimOpt.nodelay s t.
Proof.
  intros. destruct lock.
  2: { now left. }
  destruct H0; try discriminate.
  right. intro.
  left. eapply can_be_stuck_obs_state; eauto.
Qed.

Lemma lockpres_trans_nodelay_r : forall lock delay s t u,
  lockpres lock SimOpt.nodelay s t ->
  lockpres lock delay t u ->
  lockpres lock delay s u.
Proof.
  intros. destruct lock.
  2: { now left. }
  destruct H, H0; try discriminate.
  right. intro. apply H in H1. now destruct H1 as [|[? _]]; auto.
Qed.

Theorem upto_trans_l_obs :
  forall freeze lock delay (R : Chain (simF freeze lock delay)) s s' t
    (OBS : Transitive Robs),
  forall (Hobs : is_obs_state s) (Hobs' : is_obs_state s'),
  `R true s' t ->
  sim freeze lock delay true s s' ->
  `R true s t.
Proof.
  intros ????.
  apply tower. {
    intros ????????????. red.
    eapply H; eauto.
    apply leq_infx in H2. apply H2, H0.
  }
  clear R. intros R **.
  assert (TRANS : Transitive (`R true : hrel St St)^+). { typeclasses eauto. }
  clear H. set (H := True).
  constructor. apply sim_fp in H1. apply simF_equiv in H0.
  repeat split; intros; subst.
  - apply H1 in H2 as []. destruct delay.
    + apply itr_sim, (gfp_chain R) in SIM; auto.
      red in TR. rewrite str_unfold_l, dotplsx, dot1x in TR.
      destruct TR as [TR | TR]. 2: { rewrite <- dotA in TR. destruct TR. now apply Hobs' in H2. }
      apply H0 in TR as []; esim.
    + apply itr_sim, (gfp_chain R) in SIM; auto.
      apply H0 in TR; auto. destruct TR; eauto with sims.
  - now apply Hobs in H2.
  - destruct H0 as (_ & _ & ?), H1 as (_ & _ & ?); auto.
    eapply lockpres_trans_nodelay_r; eauto. eapply lockpres_obs_state_r; eauto.
Qed.

Theorem upto_trans_l :
  forall freeze lock delay (R : Chain (simF freeze lock delay)) s s' t
    (OBS : Transitive Robs),
  `R true s' t ->
  sim freeze lock SimOpt.nodelay true s s' ->
  `R true s t.
Proof.
  intros ????.
  apply tower. {
    intros ??????????. red.
    eapply H; eauto.
    apply leq_infx in H2. apply H2, H0.
  }
  clear R. intros R **.
  assert (TRANS : Transitive (`R true : hrel St St)^+). { typeclasses eauto. }
  constructor. apply sim_fp in H1. apply simF_equiv in H0.
  repeat split; intros; subst.
  - apply H1 in H2 as [].
    eapply itr_sim, sim_nodelay, (gfp_chain R) in SIM; auto.
    apply H0 in TR; auto. destruct TR; eauto with sims.
  - apply H1 in H2 as [].
    + (* tau_exact *)
      apply H0 in TR as ?; auto. destruct H2; eauto with sims.
      (* freeze_div *) subst. apply tau_div; eauto.
      eapply divpres_trans_l with (t := t'). apply DIV. apply sim_f_t; auto.
      now apply sim_nodelay.
    + (* tau_freeze *) subst freeze.
      eapply tau_freeze; eauto. eapply H; eauto. apply (b_chain R). apply simF_equiv. apply H0.
    + (* tau_div *) subst freeze.
      eapply tau_div; eauto with sims.
      eapply H; eauto. apply (b_chain R). apply simF_equiv. apply H0.
      apply simF_equiv in H0; auto. eapply simF_f_t in H0. 2: discriminate.
      apply divpres_trans_l with (s := s'0) in H0; auto. apply sim_f_t; auto.
      now apply sim_nodelay.
    + (* tau_delay *)
      discriminate.
  - destruct H0 as (_ & _ & ?), H1 as (_ & _ & ?); auto.
    eapply lockpres_trans_nodelay_r; eauto.
Qed.

Theorem upto_trans :
  forall freeze lock (Hfreeze : freeze <> SimOpt.freeze_div)
    (R : Chain (simF freeze lock SimOpt.nodelay)) s t u
    (OBS : Transitive Robs),
  `R true s t ->
  `R true t u ->
  `R true s u.
Proof.
  intros ????. apply tower. {
    intros ??????????. eapply H; eauto.
  }
  clear R. intros R **.
  apply simF_equiv in H0, H1. apply simF_equiv.
  repeat split; intros.
  - apply H0 in H2 as [].
    apply H1 in TR as [].
    econstructor; eauto. etransitivity; eauto.
  - apply H0 in H2 as []; try easy.
    + apply H1 in TR as []; try easy.
      * eapply tau_exact; eauto.
      * esim.
    + eapply tau_freeze; eauto. eapply H; eauto.
      now apply (b_chain R), simF_equiv.
  - eapply lockpres_trans_nodelay_r. apply H0. apply H1.
Qed.

End WithLTS.

Hint Constructors ObsAnswer : sims.
Hint Constructors TauAnswer : sims.
Hint Resolve dtau_plus : sims.
Hint Resolve simF_false : sims.
Hint Resolve simF_true : sims.
