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
From OptSim Require Import Utils LTS Divergence.

Import CoindNotations.

Module SimOpt.

  Variant freeze_opt := freeze_div | freeze | nofreeze.
  Variant lock_opt := lock | nolock.
  Variant delay_opt := delay | nodelay.

End SimOpt.

(*Record SimOptions :=
{
  freeze : SimOpt.freeze_opt;
  lock : SimOpt.lock_opt;
  delay : SimOpt.delay_opt;
}.*)


Section WithLTS.

Context {lts : LTS}.
Notation Observable := lts.(Observable).
Notation St := lts.(St).
Notation trans := lts.(trans).
Notation epsilon := lts.(epsilon).
Notation Robs := lts.(Robs).
Notation ub_state := lts.(ub_state).
Notation label := (@label Observable).

Section SimDef.

Context (freeze : SimOpt.freeze_opt) (lock : SimOpt.lock_opt) (delay : SimOpt.delay_opt).

Variant ObsAnswer (R : relation St) s' t o : Prop :=
| ans_obs o' t' (TR : trans (obs o') t t') (SIM : R s' t') (OBS : Robs o o') : ObsAnswer R s' t o
| ans_delay_obs o' t' (_ : delay = SimOpt.delay) (TR : ((trans tau)^* ⋅ trans (obs o')) t t') (SIM : R s' t') (OBS : Robs o o') : ObsAnswer R s' t o
.
Hint Constructors ObsAnswer : optsim.

#[export] Instance : forall R,
  Proper (St.(Eq) ==> St.(Eq) ==> impl) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> eq ==> impl) (ObsAnswer R).
Proof.
  intros. cbn. intros. subst.
  destruct H3; rewrite ?H0, ?H1 in *; eauto with optsim.
Qed.

(* delay/freeze *)
Variant TauAnswer (R : relation St) Rdiv s' t : Prop :=
| tau_exact t' (TR : trans tau t t') (SIM : R s' t')
| tau_freeze (_ : freeze = SimOpt.freeze) (SIM : R s' t)
| tau_div (_ : freeze = SimOpt.freeze_div) (SIM : R s' t) (DIV : Rdiv s' t)
| tau_delay t' (_ : delay = SimOpt.delay) (TR : (trans tau)^+ t t') (SIM : R s' t')
.
Hint Constructors TauAnswer : optsim.

#[export] Instance : forall R Rdiv,
  Proper (St.(Eq) ==> St.(Eq) ==> impl) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> impl) Rdiv ->
  Proper (St.(Eq) ==> St.(Eq) ==> impl) (TauAnswer R Rdiv).
Proof.
  intros. cbn. intros.
  destruct H3; rewrite ?H1, ?H2 in *; eauto with optsim.
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

(*Variant SimAnswer (R Rind : relation St) s' t l : Prop :=
| ans_exact l' t' (TR : trans l' t t') (SIM : R s' t') (LBL : RL l l')
| ans_freeze (_ : freeze = SimOpt.freeze) (SIM : R s' t) (LBL : l = tau)
| ans_div (_ : freeze = SimOpt.freeze_ind) (SIM : Rind s' t) (LBL : l = tau)
| ans_delay l' t' (_ : delay = SimOpt.delay) (TR : ((trans tau)^+ ⋅ trans l') t t') (SIM : R s' t') (LBL : RL l l')
.
Hint Constructors SimAnswer : optsim.

#[export] Instance : forall R Rind,
  Proper (St.(Eq) ==> St.(Eq) ==> iff) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> iff) Rind ->
  Proper (St.(Eq) ==> St.(Eq) ==> eq ==> flip impl) (SimAnswer R Rind).
Proof.
  intros. cbn. intros. subst.
  destruct H4; rewrite <- ?H1, <- ?H2 in *; eauto with optsim.
Qed.*)

(*
Definition sim_alt R s t :=
  (forall l s', trans l s s' ->
    match l with
    | obs o => ObsAnswer R s' t o
    | tau => TauAnswer R (simInd R) s' t
    end) /\
  (lock = SimOpt.nolock \/ (is_stuck s -> is_stuck t)).

Lemma sim_alt_equiv : forall R s t, simInd R s t <-> sim_alt R s t.
Proof.
  split; intro.
  - destruct H as [(? & ? & ?)].
    split; auto. intros.
    destruct l; auto.
  - destruct H. repeat split; auto; intros.
    + now apply H in H1.
    + now apply H in H1.
Qed.

Definition sim_alt' R s t :=
  (forall l s', trans l s s' -> SimAnswer R (simInd R) s' t l) /\
  (lock = SimOpt.nolock \/ (is_stuck s -> is_stuck t)).

Lemma sim_alt'_equiv : forall R s t, sim_alt R s t <-> sim_alt' R s t.
Proof.
  split; intro.
  - destruct H.
    split; auto. intros.
    apply H in H1.
    destruct l; destruct H1; eauto with optsim.
    + rewrite str_itr, dotplsx, dot1x in TR.
      destruct TR as [TR | TR]; eauto with optsim.
    + rewrite itr_unfold_r in TR; eauto.
      destruct TR as [TR | TR]; eauto with optsim.
  - destruct H. split; auto; intros.
    apply H in H1.
    destruct l; destruct H1; (try destruct l');
      try discriminate; eauto with optsim exfalso.
    + eright; eauto. now rewrite <- str_itr'.
    + econstructor 4; eauto. now rewrite itr_unfold_r, <- leq_cup_r.
Qed.
*)

Definition simGame R s t := (forall o s', trans (obs o) s s' -> ObsAnswer (R true) s' t o) /\
  (forall s', trans tau s s' -> TauAnswer (R true) (R false) s' t) /\
  (lock = SimOpt.nolock \/ (is_stuck s -> is_stuck t)).

Variant simF_ R : bool -> St -> St -> Prop :=
| simF_game s t : simGame R s t -> simF_ R true s t
(*| sim_ub*)
| simF_divpres s t : divpresF (R false) s t -> simF_ R false s t.

Program Definition simF :
  mon (bool -> St -> St -> Prop) :=
{| body R b s t :=
  simF_ R b s t
|}.
Next Obligation.
  destruct H0; constructor; repeat split; intros.
  - apply H0 in H1 as []; esim.
  - apply H0 in H1 as []; esim.
  - now apply H0.
  - eapply (Hbody divpresF). 2: { apply H0. } cbn. intros. now apply H.
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

Definition sim := gfp simF.

Lemma simF_false : forall R s t,
  simF R false s t ->
  divpresF (R false) s t.
Proof.
  intros. now inversion H.
Qed.
Hint Resolve simF_false : optsim.

Lemma simF_true : forall R s t,
  simF R true s t ->
  simGame R s t.
Proof.
  intros. now inversion H.
Qed.
Hint Resolve simF_true : optsim.

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
Hint Resolve dtau_plus : optsim.

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

Definition upto_refl `{Reflexive _ Robs} b :
  Reflexive (`R b).
Proof.
  apply tower.
  - firstorder.
  - destruct b; constructor; esim. repeat split; esim.
Qed.

(* adds a tau on the right *)
(*Theorem upto_tau_r' :
  forall s t t'
    (Hfreeze : freeze = SimOpt.freeze),
  (trans tau t t' /\ forall l t'', trans l t t'' -> l = tau /\ t'' = t') ->
  `R true s t ->
  `R true s t'.
Proof.
  apply tower. {
    intros ? INC s t t' ?????. red.
    eapply INC; auto.
    apply H.
    apply leq_infx in H1.
    now apply H1.
  }
  intros. destruct H0. repeat split; intros.
  + (* observable event *)
    destruct H1. apply H1 in H3 as [].
    * now apply H2 in TR as [? _].
    * eright; eauto.
      rewrite str_itr, dotplsx in TR. destruct TR as [TR | TR].
      { rewrite dot1x in TR. now apply H2 in TR. }
      rewrite itr_str_l in TR. rewrite <- dotA in TR. destruct TR as [t0 TR1 TR2].
      apply H2 in TR1 as [_ ->]. apply TR2.
  + (* tau*)
    intros. apply H1 in H3 as [].
    * apply H2 in TR as [_ ->]. econstructor 2; eauto.
    * econstructor 2; eauto.
    * now rewrite Hfreeze in H3.
    * rewrite itr_str_l in TR. destruct TR as [t0 TR1 TR2].
      apply H2 in TR1 as [_ ->]. eapply tau_weak; eauto. typeclasses eauto.
  + (* deadlock *)
    destruct H1 as (_ & _ & []); auto.
    right. intro. apply H1 in H3. intro. eauto with optsim.
Qed.

Theorem upto_tau_r'' :
  forall s t t' t0,
  trans tau t t' ->
  (trans tau t0 t' /\ forall l t'', trans l t0 t'' -> l = tau /\ St.(Eq) t'' t') ->
  `R s t0 ->
  `R s t.
Proof.
  apply tower. {
    intros ? INC s t t' ??????. red.
    eapply INC; eauto.
    now apply H1.
  }
  intros. repeat split; intros; subst.
  + (* observable event *)
    apply H0 in H3 as [].
    * eleft; eauto. now apply H2 in TR as [? _].
    * eright; eauto. rewrite str_itr, dotplsx, dot1x in TR |- *.
      destruct TR; [left | right].
      now apply H2 in H4 as [? _].
      destruct H4. admit.
  + (* tau *)
    apply H0 in H3 as [].
    * apply H2 in TR as [_ ?]. rewrite H3 in SIM.
      econstructor 1; eauto.
    * apply tau_freeze; auto. eapply H; eauto.
    * apply tau_div; auto. apply SIM; auto.
    * econstructor 4; eauto.
      rewrite itr_str_l in TR |- *. admit.
  + (* deadlock *)
    destruct H0 as (_ & _ & []); auto.
    right. intros. apply H0 in H3.
    intro. apply H3. econstructor; eapply H2.
Admitted.
*)

Theorem sim_tau_l (Hfreeze : freeze = SimOpt.freeze_div) :
  forall b s t,
  is_tau_state s ->
  forall (Hstuck : extrans s),
  (forall s', trans tau s s' -> `R b s' t) ->
  `R b s t.
Proof.
  apply tower. {
    intros ??????????. apply H; auto.
    intros. apply H1; auto.
  }
  clear R. intros R **. destruct b.
  - constructor.
    repeat split; intros.
    + now apply H0 in H2.
    + apply H1 in H2. apply tau_div; auto. apply (b_chain R). apply H2.
      apply simF_f_t; auto. now rewrite Hfreeze.
    + esim.
  - constructor. constructor.
    intros ??.
    apply H1 in H2 as ?. apply simF_equiv in H3. destruct H3.
    eapply dtau_div; eauto. constructor. apply H3.
Qed.

Theorem upto_tau_r :
  forall s t t'
    (* FIXME with the right def, no need for Hstuck *)
    (Hstuck : extrans s \/ lock = SimOpt.nolock) (* \/ taustar_det t t' *)
    (Hdelay : delay = SimOpt.delay),
  (trans tau)^* t t' ->
  `R true s t' ->
  `R true s t.
Proof.
  apply tower. {
    intros ? INC s t t' ??????. red.
    eapply INC; auto.
    apply H.
    apply leq_infx in H1.
    now apply H1.
  }
  intros. constructor. apply simF_equiv in H1.
  repeat split; intros; subst.
  + (* observable event *)
    apply H1 in H2 as [].
    * eright; eauto. esplit; eauto.
    * eright; auto. 2: apply SIM. 2: apply OBS. destruct TR. esplit. 2: apply H4.
      rewrite <- str_trans. esplit; eassumption.
  + (* tau *)
    apply H1 in H2 as [].
    * econstructor 4; eauto.
      rewrite itr_str_r. esplit; eauto.
    * eapply tau_weak; eauto with optsim. typeclasses eauto.
    * eapply tau_weak_div; eauto with optsim; typeclasses eauto.
    * econstructor 4; eauto.
      rewrite itr_str_r, <- str_trans, <- dotA, <- itr_str_r.
      esplit; eauto.
  + (* deadlock *)
    destruct Hstuck as [Hstuck|]; auto.
    right. intros. now apply H2 in Hstuck.
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
  - eapply upto_tau_r; eauto. admit. now rewrite <- str_ext.
  - apply SIM.
  - apply SIM.
  - eapply upto_tau_r; eauto. admit. rewrite str_itr. now right.
Admitted.

End SimUpTo.

Theorem sim_tau_r :
  forall s t t'
    (Hlock : extrans s \/ lock = SimOpt.nolock) (* \/ taustar_det t t' *)
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
  - cbn. intros. now rewrite H0, H1.
  - intros. rewrite <- H0. apply H1.
  - intros. apply H1. eapply sim_inv_tau_l; eauto.
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

End SimDef.

Hint Constructors ObsAnswer : optsim.
Hint Constructors TauAnswer : optsim.
Hint Resolve dtau_plus : optsim.
Hint Resolve simF_false : optsim.
Hint Resolve simF_true : optsim.

(* Up-to principles with heterogeneous options *)

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

Theorem upto_sim_r :
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
  - apply H0 in H2 as []; auto.
    + apply sim_fp in H1.
      apply H1 in TR. destruct TR; eauto with optsim.
    + destruct TR as [t'' TR1 TR2].
      subst. eapply sim_inv_taustar_l in H1; eauto.
      apply sim_fp in H1.
      apply H1 in TR2; auto. destruct TR2; eauto with optsim.
  - apply H0 in H2 as []; auto.
    + (* tau_exact *) apply sim_fp in H1.
      apply H1 in TR as ?. destruct H2; eauto with optsim.
      * (* freeze *) destruct freeze; try discriminate.
        apply tau_freeze; auto. eapply H; eauto.
      * (* freeze_div *) destruct freeze; discriminate.
    + (* tau_freeze *) subst freeze.
      eapply tau_freeze; eauto.
    + (* tau_div *) subst freeze.
      eapply tau_div; eauto with optsim.
      eapply divpres_nofreeze_r; eauto.
    + (* tau_delay *)
      rewrite itr_str_r in TR. destruct TR as [t'1 TR1 TR2].
      subst.
      eapply sim_inv_taustar_l in H1; eauto.
      apply sim_fp in H1.
      apply H1 in TR2; auto.
      destruct freeze; destruct TR2; try discriminate; eauto with optsim.
  - destruct H0. apply sim_fp in H1 as (_ & _ & ?); auto. intuition.
Qed.

Theorem upto_sim_l :
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
  intros. constructor. apply sim_fp in H1. apply simF_equiv in H0.
  repeat split; intros; subst.
  - apply H1 in H2 as [].
    + apply H0 in TR; auto. destruct TR; eauto with optsim.
    + discriminate.
  - apply H1 in H2 as [].
    + (* tau_exact *)
      apply H0 in TR as ?; auto. destruct H2; eauto with optsim.
      (* freeze_div *) subst. apply tau_div; eauto.
      eapply divpres_trans_l with (t := t'). apply DIV. apply sim_f_t; auto. admit.
    + (* tau_freeze *) subst freeze.
      eapply tau_freeze; eauto. eapply H; eauto. apply (b_chain x). apply simF_equiv. apply H0.
    + (* tau_div *) subst freeze.
      eapply tau_div; eauto with optsim.
      eapply H; eauto. apply (b_chain x). apply simF_equiv. apply H0.
      apply simF_equiv in H0; auto. eapply simF_f_t in H0. 2: discriminate.
      apply divpres_trans_l with (s := s'0) in H0; auto. apply sim_f_t; auto. admit.
    + (* tau_delay *)
      discriminate.
  - destruct H0 as (_ & _ & ?), H1 as (_ & _ & ?); auto. intuition.
Admitted.

(*
Lemma wsim_obs' :
  forall s t
    (Hstuck : extrans s \/ lock = SimOpt.nolock),
  is_obs_state s ->
  (forall o s', trans (obs o) s s' -> exists o' tt' t', trans (obs o') t t' /\ `R s' (tt') /\ Robs o o' /\ trans tau tt' t') ->
  wsimF div lock exp ub `R s t.
Proof.
  intros. repeat split; intros; subst.
  - apply H0 in H1 as (? & ? & ? & ? & ? & ? & ?).
    exists x, x1. split. admit. split; auto.
  - now apply H in H1.
  - now eapply diverges_obs_state in H2.
  - destruct Hstuck; try discriminate.
    now apply H2 in H1.
Qed.

Lemma wsim_obs :
  forall s t
    (Hstuck : extrans s \/ lock = SimOpt.nolock),
  is_obs_state s ->
  (forall o s', trans (obs o) s s' -> exists o' t', trans (obs o') t t' /\ `R s' t' /\ Robs o o') ->
  wsimF div lock exp ub `R s t.
Proof.
  intros. repeat split; intros; subst.
  - apply H0 in H1 as (? & ? & ? & ? & ?). eauto 6 with optsim.
  - now apply H in H1.
  - now eapply diverges_obs_state in H2.
  - destruct Hstuck; try discriminate.
    now apply H2 in H1.
Qed.

Lemma wsim_tau :
  forall s t
    (Hstuck : extrans s \/ is_stuck t \/ lock = SimOpt.nolock), (* basically the definition of complete sim *)
  is_tau_state s ->
  (forall s', trans tau s s' -> exists t', taustar t t' /\ `R s' t) ->
  wsimF div lock exp ub `R s t.
Proof.
  intros. repeat split; intros; subst.
  - now apply H in H1.
  - admit.
  - (* this obviously won't work *)
    apply (gfp_fp divergesF) in H2 as (? & ? & ?).
    apply H0 in H1 as ?.
    admit.
  - destruct Hstuck as [|[|]]; try discriminate.
    now apply H2 in H1.
    apply H1.
Abort.
*)

End WithLTS.

Hint Constructors ObsAnswer : optsim.
Hint Constructors TauAnswer : optsim.
Hint Resolve dtau_plus : optsim.
Hint Resolve simF_false : optsim.
Hint Resolve simF_true : optsim.
