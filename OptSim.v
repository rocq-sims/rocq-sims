From Coq Require Import Init Program.Equality.
From Coinduction Require Import all.
From RelationAlgebra Require Import
     monoid
     kat
     kat_tac
     prop
     rel
     srel
     comparisons
     rewriting
     normalisation.

Import CoindNotations.

Module LTS.

  Parameter Observable : Set.
  Variant label := obs (s : Observable) | tau.
  Parameter St : EqType.
  Parameter trans : label -> srel St St.
  Parameter epsilon : srel St St.
  Parameter Robs : Observable -> Observable -> Prop.
  Parameter ub_state : St -> Prop. (* FIXME Proper *)
  (*Parameter eq : St -> St -> Prop.*)

End LTS.

Variant label {S : Set} := obs (s : S) | tau.

Module LockLTS.

  Variant Observable := | Event (e : LTS.Observable) | NoEvent.
  Definition St := (bool * LTS.St)%type.
  Variant trans : @label Observable -> St -> St -> Prop :=
  (*| trans_ev l s t : LTS.trans l s t -> trans (Event l) s t*)
  | trans_noev s : (forall l t, LTS.trans l s t -> False) -> trans (obs NoEvent) (true, s) (true, s)
  .
  Definition epsilon : St -> St -> Prop :=
    fun '(b, s) '(b', s') =>
    LTS.epsilon s s' /\ (
      (b = false /\ b' = false) \/
      (b = true /\ b' = false) \/
      (b = true /\ b' = true /\ forall l s'', LTS.trans l s s'' -> False)
    ).
  Definition Robs : Observable -> Observable -> Prop. Admitted.
  Definition ub_state : St -> Prop. Admitted.
  (*Parameter eq : St -> St -> Prop.*)

End LockLTS.

Import LTS.
(*#[export] Instance trans_rewrite l : Proper (St.(Eq) ==> St.(Eq) ==> iff) (trans l).
Proof.
  typeclasses eauto.
Qed.*)

#[global] Instance : Proper (weq ==> eq ==> eq ==> iff) (hrel_of (n := St) (m := St)).
Proof.
  cbn. intros. subst. apply H.
Qed.

#[global] Instance : Proper (leq ==> eq ==> eq ==> impl) (hrel_of (n := St) (m := St)).
Proof.
  cbn. intros. subst. now apply H.
Qed.

Definition is_obs (l : label) := if l then true else false.
Definition is_tau (l : label) := if l then false else true.

Definition is_tau_state st :=
  forall l st', trans l st st' -> is_tau l = true.

Definition is_obs_state st :=
  forall l st', trans l st st' -> is_obs l = true.

(*(* P is true after a certain amount of tau steps *)
Inductive taustarP (P : St -> Prop) : St -> Prop :=
| taustarP_id s : P s -> taustarP P s
| taustarP_tau s s' : trans tau s s' -> taustarP P s' -> taustarP P s.

(*Definition taustar s s' := taustarP (fun s => s = s') s.*)

Inductive taustar : St -> St -> Prop :=
| taustar_id s : taustar s s
| taustar_tau s s' s'' : trans tau s s' -> taustar s' s'' -> taustar s s''.

Definition wtrans l s s' :=
  exists s0 s1, taustar s s0 /\ trans l s0 s1 /\ taustar s1 s'.*)

Create HintDb optsim.
#[local] Ltac esim := eauto 10 with optsim.
(*#[export] Hint Constructors taustar : optsim.
#[export] Hint Unfold wtrans : optsim.*)

(*Lemma trans_wtrans : forall l s s',
  trans l s s' -> wtrans l s s'.
Proof.
  intros. exists s, s'. repeat split; auto with optsim.
Qed.
#[export] Hint Resolve trans_wtrans : optsim.

#[export] Instance Transitive_taustar : Transitive taustar.
Proof.
  red. intros. induction H; auto.
  apply IHtaustar in H0.
  eright; eauto.
Qed.

Lemma taustar_wtrans : forall l s s' s'',
  taustar s s' -> wtrans l s' s'' -> wtrans l s s''.
Proof.
  intros.
  destruct H0 as (? & ? & ? & ? & ?).
  exists x, x0; repeat split; auto.
  etransitivity; eauto.
Qed.*)

Module WSOpt.

  Variant compress_opt := compress_ind | compress_coind | nocompress.
  Definition div := compress_ind.
  Variant lock_opt := lock | nolock.
  Variant expand_opt := expand | noexpand.
  Variant ub_opt := noub | ub | ttub. (* TODO can non-TT UB be characterized just as "every transition is possible"? *)

End WSOpt.

Program Definition divergesF : mon (St -> Prop) :=
{| body R st :=
  exists st', trans tau st st' /\ R st'
|}.
Next Obligation.
  eauto.
Qed.

Definition diverges := gfp divergesF.

Definition extrans (st : St) : Prop :=
  exists l st', trans l st st'.

#[export] Instance : Proper (St.(Eq) ==> flip impl) extrans.
Proof.
  cbn. unfold extrans. intros. now setoid_rewrite H.
Qed.

Definition is_stuck (st : St) : Prop :=
  ~ extrans st.

#[export] Instance : Proper (St.(Eq) ==> flip impl) is_stuck.
Proof.
  cbn. unfold is_stuck. intros. now setoid_rewrite H.
Qed.

(*Inductive ws_delay
  (P : St -> St -> Prop) : St -> St -> Prop :=
| wsd_d s s' t : ws_delay P s' t -> trans tau s s' -> ws_delay P s t
| wsd_id s t : P s t -> ws_delay P s t.*)

From RelationAlgebra Require Import
     monoid.

Section SimDef.

Context (compress : WSOpt.compress_opt)
  (lock : WSOpt.lock_opt)
  (expand : WSOpt.expand_opt)
  (ub : WSOpt.ub_opt).

Variant ObsAnswer (R : relation St) s' t o : Prop :=
| ans_obs o' t' (TR : trans (obs o') t t') (SIM : R s' t') (OBS : Robs o o') : ObsAnswer R s' t o
| ans_delay_obs o' t' (_ : expand = WSOpt.expand) (TR : ((trans tau)^* ⋅ trans (obs o')) t t') (SIM : R s' t') (OBS : Robs o o') : ObsAnswer R s' t o
.
Hint Constructors ObsAnswer : optsim.

#[export] Instance : forall R,
  Proper (St.(Eq) ==> St.(Eq) ==> iff) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> eq ==> flip impl) (ObsAnswer R).
Proof.
  intros. cbn. intros. subst.
  destruct H3; rewrite <- ?H0, <- ?H1 in *; eauto with optsim.
Qed.

(* delay/freeze *)
Variant TauAnswer (R Rind : relation St) s' t : Prop :=
| tau_exact t' (TR : trans tau t t') (SIM : R s' t')
| tau_compress (_ : compress = WSOpt.compress_coind) (SIM : R s' t)
| tau_div (_ : compress = WSOpt.compress_ind) (SIM : Rind s' t)
| tau_expand t' (_ : expand = WSOpt.expand) (TR : (trans tau)^+ t t') (SIM : R s' t')
.
Hint Constructors TauAnswer : optsim.

#[export] Instance : forall R Rind,
  Proper (St.(Eq) ==> St.(Eq) ==> iff) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> iff) Rind ->
  Proper (St.(Eq) ==> St.(Eq) ==> flip impl) (TauAnswer R Rind).
Proof.
  intros. cbn. intros.
  destruct H3; rewrite <- ?H1, <- ?H2 in *; eauto with optsim.
Qed.

Lemma tau_weak :
  compress = WSOpt.compress_coind ->
  expand = WSOpt.expand ->
  forall R Rind s' t t',
  Proper (St.(Eq) ==> St.(Eq) ==> iff) R ->
  (trans tau)^* t t' -> R s' t' -> TauAnswer R Rind s' t.
Proof.
  intros -> -> * ? TR SIM.
  rewrite str_itr in TR. destruct TR as [TR | TR].
  - cbn in TR. apply tau_compress; auto. now rewrite TR.
  - eapply tau_expand; eauto.
Qed.

Lemma tau_weak_div :
  compress = WSOpt.compress_ind ->
  expand = WSOpt.expand ->
  forall R Rind s' t t',
  Proper (St.(Eq) ==> St.(Eq) ==> iff) Rind ->
  subrelation Rind R ->
  (trans tau)^* t t' -> Rind s' t' -> TauAnswer R Rind s' t.
Proof.
  intros -> -> * ?? TR SIM.
  rewrite str_itr in TR. destruct TR as [TR | TR].
  - cbn in TR. apply tau_div; auto. now rewrite TR.
  - eapply tau_expand; eauto.
Qed.

Definition RL l l' :=
  match l, l' with
  | tau, tau => True
  | obs o, obs o' => Robs o o'
  | _, _ => False
  end.

Variant SimAnswer (R Rind : relation St) s' t l : Prop :=
| ans_exact l' t' (TR : trans l' t t') (SIM : R s' t') (LBL : RL l l')
| ans_compress (_ : compress = WSOpt.compress_coind) (SIM : R s' t) (LBL : l = tau)
| ans_div (_ : compress = WSOpt.compress_ind) (SIM : Rind s' t) (LBL : l = tau)
| ans_expand l' t' (_ : expand = WSOpt.expand) (TR : ((trans tau)^* ⋅ trans l') t t') (SIM : R s' t') (LBL : RL l l')
.
Hint Constructors SimAnswer : optsim.

#[export] Instance : forall R Rind,
  Proper (St.(Eq) ==> St.(Eq) ==> iff) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> iff) Rind ->
  Proper (St.(Eq) ==> St.(Eq) ==> eq ==> flip impl) (SimAnswer R Rind).
Proof.
  intros. cbn. intros. subst.
  destruct H4; rewrite <- ?H1, <- ?H2 in *; eauto with optsim.
Qed.

Definition simIndF R Rind s t :=
  (forall o s', trans (obs o) s s' ->
    ObsAnswer R s' t o
    (*exists o' t',
        (trans (obs o') t t' \/
        (expand = WSOpt.expand /\ ((trans tau)^* ⋅ trans (obs o')) t t')) /\
      R s' t' /\
      Robs o o'*)
  ) /\
  (forall s', trans tau s s' ->
    TauAnswer R Rind s' t
  (*exists t', 
    ((trans tau t t' /\ R s' t') \/
    (compress = WSOpt.compress_coind /\ St.(Eq) t t' /\ R s' t') \/
    (compress = WSOpt.compress_ind /\ St.(Eq) t t' /\ simInd R s' t') \/
    (expand = WSOpt.expand /\ (trans tau)^+ t t' /\ R s' t')
    )*)) /\
  (lock = WSOpt.nolock \/ (is_stuck s -> is_stuck t)) (* FIXME tau* in answer *).

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
    eleft; eauto.
    eright; eauto.
  - apply H0 in H1 as []; esim.
  - apply H0.
Qed.

Definition sim_alt R s t :=
  (forall l s', trans l s s' ->
    match l with
    | obs o => ObsAnswer R s' t o
    | tau => TauAnswer R (simInd R) s' t
    end) /\
  (lock = WSOpt.nolock \/ (is_stuck s -> is_stuck t)).

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
  (lock = WSOpt.nolock \/ (is_stuck s -> is_stuck t)).

Lemma sim_alt'_equiv : forall R s t, sim_alt R s t <-> sim_alt' R s t.
Proof.
  split; intro.
  - destruct H.
    split; auto. intros.
    apply H in H1.
    destruct l; destruct H1; eauto with optsim.
    econstructor 4; eauto.
    + now rewrite <- itr_str_r.
    + constructor.
  - destruct H. split; auto; intros.
    apply H in H1.
    destruct l; destruct H1; (try destruct l');
      try discriminate; eauto with optsim exfalso.
    rewrite <- itr_str_r in TR. eauto with optsim.
Qed.

(*Inductive sim R Rind s t := mkSim
{
  sim_obs : (forall o s', trans (obs o) s s' ->
    ObsAnswer R s' t o
    (*exists o' t',
        (trans (obs o') t t' \/
        (expand = WSOpt.expand /\ ((trans tau)^* ⋅ trans (obs o')) t t')) /\
      R s' t' /\
      Robs o o'*)
  );
  sim_tau : (forall s', trans tau s s' ->
    TauAnswer R Rind s' t
  (*exists t', 
    ((trans tau t t' /\ R s' t') \/
    (compress = WSOpt.compress_coind /\ St.(Eq) t t' /\ R s' t') \/
    (compress = WSOpt.compress_ind /\ St.(Eq) t t' /\ Rind s' t') \/
    (expand = WSOpt.expand /\ (trans tau)^+ t t' /\ R s' t')
    )*));
  sim_lock : lock = WSOpt.nolock \/ (is_stuck s -> is_stuck t)
}.
Hint Constructors sim : optsim.

Inductive simInd R : St -> St -> Prop :=
| simI s t : sim R (simInd R) s t -> simInd R s t
.
Hint Constructors simInd : optsim.
Print simInd_ind.
Definition simInd_ind' : forall (R : relation St) (P : St -> St -> Prop)
  (f0 : compress = WSOpt.compress_ind -> forall s t, (forall s', trans tau s s' -> P s' t) -> P s t)
  (f1 : forall (s t : St), sim R R s t -> P s t) (t t0 : St)
  (s : simInd R t t0),
  P t t0.
Proof.
  intros ????. refine (fix F s t (SIM : simInd R s t) {struct SIM} : P s t := _).
  destruct SIM.
  destruct H.
  destruct compress.
  - specialize (f0 eq_refl).
    eapply f0. intros. apply sim_tau0 in H. dependent destruction H. admit. admit. apply F. apply SIM. eapply s; eauto.
  refine (match SIM with
  | {| sim_tau := _ |} => _
  end).
  fix s 7. intros. eapply s. 3: apply s0.
  destruct s0, H; intros.
  - eapply f0; eauto.
  - apply f1.
Qed.
  destruct sim_tau0.
  refine (match s in (simInd _ t1 t2) return (P t1 t2) with
  | simI R s0 t1 x => _
  end).
*)

Lemma simInd_mon : forall R R', R <= R' -> simInd R <= simInd R'.
Proof.
  cbn. intros. induction H0.
  repeat split; intros.
  - apply H0 in H1 as []; esim.
  - apply H0 in H1 as []; esim.
    destruct SIM. esim.
  - apply H0.
Qed.

Program Definition simF :
  mon (St -> St -> Prop) :=
{| body R s t :=
  simInd R s t
|}.
Next Obligation.
  eapply simInd_mon. 2: apply H0. cbn. apply H.
Qed.

#[export] Instance simF_eq R :
  Proper (Eq St ==> Eq St ==> iff) R ->
  Proper (Eq St ==> Eq St ==> flip impl) (simInd R).
Proof.
  intros. cbn. intros. revert x x0 H0 H1. induction H2. intros. destruct H0 as (? & ? & ?).
  constructor. repeat split; intros; rewrite ?H1, ?H2 in * |- *; auto.
  apply H3 in H5. destruct H5; rewrite <- ?H1, <- ?H2 in * |- *; eauto with optsim.
  econstructor 3; auto. destruct SIM. apply H7; auto.
Qed.

#[export] Instance Chain_simF_eq : forall (R : Chain simF),
  Proper (Eq St ==> Eq St ==> iff) ` R.
Proof.
  intro. apply tower. {
    intros ? INC ??????. split; intros ???.
    - eapply INC. assumption.
      now rewrite <- H. now rewrite <- H0.
      now apply H1.
    - eapply INC. assumption.
      now rewrite H. now rewrite H0.
      now apply H1.
  }
  intros. split; intro.
  now rewrite H0, H1 in H2.
  now rewrite H0, H1.
Qed.

Definition sim := gfp simF.

Section SimUpTo.

Context (*(div : WSOpt.div_opt) (lock : WSOpt.lock_opt)
  (exp : WSOpt.exp_opt) (ub : WSOpt.ub_opt)*)
  (R : Chain simF).

Definition upto_refl `{Reflexive _ Robs} :
  Reflexive `R.
Proof.
  apply tower.
  - firstorder.
  - repeat split; intros; auto.
    + eauto 8 with optsim.
    + eauto with optsim.
Qed.

(*Lemma diverges_taustar :
  forall s s', diverges s' -> taustar s s' -> diverges s.
Proof.
  intros. induction H0; auto.
  apply (gfp_fp divergesF). cbn.
  exists s'. split; auto. now apply IHtaustar.
Qed.

Lemma diverges_obs_state :
  forall st, is_obs_state st -> diverges st -> False.
Proof.
  intros.
  apply (gfp_fp divergesF) in H0 as (? & ? & _).
  now apply H in H0.
Qed.*)

Lemma str_itr' : forall (l : level) (X : ops),
  laws l X -> KA ≪ l -> forall (n : ob X) (x : X n n), x^+ ≦ x^*.
Proof.
  intros. now rewrite str_itr, <- leq_cup_r.
Qed.

(* adds a tau on the right *)
Theorem upto_tau_r' :
  forall s t t'
    (Hcompress : compress = WSOpt.compress_coind),
  (trans tau t t' /\ forall l t'', trans l t t'' -> l = tau /\ t'' = t') ->
  `R s t ->
  `R s t'.
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
    intros. destruct H1. apply H1 in H3 as [].
    * apply H2 in TR as [_ ->]. econstructor 2; eauto.
    * econstructor 2; eauto.
    * now rewrite Hcompress in H3.
    * rewrite itr_str_l in TR. destruct TR as [t0 TR1 TR2].
      apply H2 in TR1 as [_ ->]. eapply tau_weak; eauto. typeclasses eauto.
  + (* deadlock *)
    destruct H1 as [(_ & _ & [])]; auto.
    right. intro. apply H1 in H3. (*now apply H3 in H0.*) admit.
Admitted.

Theorem upto_tau_r'' :
  forall s t t' t0
    (*(Hstuck : extrans s \/ lock = WSOpt.nolock)*) (* \/ taustar_det t t' *),
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
  intros. revert t H0 H1. induction H2. repeat split; intros; subst.
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
    * apply tau_compress; auto. eapply H; eauto.
    * apply tau_div; auto. apply SIM; auto.
    * econstructor 4; eauto.
      rewrite itr_str_l in TR |- *. admit.
  + (* deadlock *)
    destruct H0 as (_ & _ & []); auto.
    right. intros. apply H0 in H3.
    intro. apply H3. eexists _, _; eapply H2.
Admitted.

Theorem upto_tau_r :
  forall s t t'
    (Hstuck : extrans s \/ lock = WSOpt.nolock) (* \/ taustar_det t t' *)
    (Hexpand : expand = WSOpt.expand),
  (trans tau)^* t t' ->
  `R s t' ->
  `R s t.
Proof.
  apply tower. {
    intros ? INC s t t' ??????. red.
    eapply INC; auto.
    apply H.
    apply leq_infx in H1.
    now apply H1.
  }
  intros. repeat split; intros; subst.
  + (* observable event *)
    destruct H1. apply H1 in H2 as [].
    * eright; eauto. esplit; eauto.
    * eright; auto. 2: apply SIM. 2: apply OBS. destruct TR. esplit. 2: apply H4.
      rewrite <- str_trans. esplit; eassumption.
  + (* tau *)
    destruct H1. apply H1 in H2 as [].
    * econstructor 4; eauto.
      rewrite itr_str_r. esplit; eauto.
    * eapply tau_weak; eauto with optsim. typeclasses eauto.
    * eapply tau_weak_div; eauto with optsim.
      epose proof simF_eq.
      assert (forall R : St -> St -> Prop,
      Proper (Eq St ==> Eq St ==> iff) R ->
      Proper (Eq St ==> Eq St ==> impl) (simInd R)) by admit. Search Proper impl iff.
      apply proper_sym_impl_iff_2; try typeclasses eauto.
      red. intros. now step.
    * econstructor 4; eauto.
      rewrite itr_str_r, <- str_trans, <- dotA, <- itr_str_r.
      esplit; eauto.
  + (* deadlock *)
    destruct Hstuck as [Hstuck|]; auto.
    right. intros. now apply H2 in Hstuck.
Admitted.

(* useless if compress_coind is set *)
Theorem inv_tau_l :
  forall s s' t
    (*(Hstuck : extrans s \/ lock = WSOpt.nolock)*) (* \/ taustar_det t t' *)
    (Hexpand : expand = WSOpt.expand),
  trans tau s s' ->
  simF `R s t ->
  `R s' t.
Proof.
  (*apply tower. {
    intros ? INC s t t' ?????. red.
    eapply INC; auto.
    apply H.
    apply leq_infx in H1.
    now apply H1.
  }*)
  intros. apply sim_alt_equiv in H0.
  destruct H0 as [SIM STUCK].
  apply SIM in H as [].
  - eapply upto_tau_r; eauto. admit. now rewrite <- str_ext.
  - apply SIM0.
  - step. apply SIM0.
  - eapply upto_tau_r; eauto. admit. rewrite str_itr. now right.
Admitted.

End SimUpTo.
End SimDef.

Theorem sim_inv_tau_l :
  forall compress lock expand s s' t
    (*(Hstuck : extrans s \/ lock = WSOpt.nolock)*) (* \/ taustar_det t t' *)
    (Hexpand : expand = WSOpt.expand),
  trans tau s s' ->
  sim compress lock expand s t ->
  sim compress lock expand s' t.
Proof.
  intros. red. apply (gfp_fp (simF _ _ _)) in H0. eapply inv_tau_l in H0; eauto. admit.
Admitted.

Hint Constructors ObsAnswer : optsim.
Hint Constructors TauAnswer : optsim.

Theorem upto_sim_r :
  forall compress lock expand (R : Chain (simF compress lock expand)) s t t'
    (OBS : Transitive Robs),
  `R s t' ->
  sim (match compress with WSOpt.compress_ind => WSOpt.nocompress | _ => compress end) lock expand t' t ->
  `R s t.
Proof.
  intros ????.
  apply tower. {
    intros ??????????. red.
    eapply H; eauto.
    apply leq_infx in H2. apply H2, H0.
  }
  intros.
  repeat split; intros; subst.
  - destruct H0. apply H0 in H2 as [].
    + apply (gfp_fp (simF _ _ _)) in H1. destruct H1.
      apply H1 in TR. destruct TR.
      * eleft; eauto.
      * eright; eauto.
    + destruct TR as [t'' TR1 TR2].
      destruct TR1. clear H0. assert (H0 : True) by apply I. revert t' H0 H1 H3. induction x0; intros.
      * cbn in H3. rewrite <- H3 in TR2.
        apply (gfp_fp (simF _ _ _)) in H1. apply H1 in TR2.
        destruct TR2.
        --eleft; info_eauto.
        --eright; info_eauto.
      * cbn in H3. destruct H3. eapply sim_inv_tau_l in H1; eauto.
  - destruct H0. apply H0 in H2 as [].
    + (* tau_exact *) apply (gfp_fp (simF _ _ _)) in H1. destruct H1.
      apply H1 in TR as ?. destruct H2; eauto with optsim.
      * (* compress_coind *) destruct compress; try discriminate. apply tau_compress; auto. eapply H; eauto.
      * (* compress_ind *) destruct compress; discriminate.
    + (* tau_compress *) subst compress.
      eapply tau_compress; eauto.
    + (* tau_div *) subst compress.
      eapply tau_div; auto. admit. (* induction *)
    + (* tau_expand *)
      assert (exists t1, (trans tau)^+ t t1 /\ sim WSOpt.nocompress lock expand t'0 t1) by admit. (* /\ n' <= n *)
      destruct H3. eapply tau_expand; auto. apply H3. eapply H; auto. apply SIM. admit.
  - destruct H0. apply (gfp_fp (simF _ _ _)) in H1 as [(_ & _ & ?)]. intuition.
Admitted.

(* direct definition of divergence-sensitive weak simulation *)
Program Definition divsimF lock : mon (St -> St -> Prop) :=
{|
  body := fun R s t => (forall o s', ((trans tau)^* ⋅ trans (obs o)) s s' ->
    exists o' t',
        ((trans tau)^* ⋅ trans (obs o')) t t' /\
      R s' t' /\
      Robs o o') /\
  (forall s', (trans tau)^* s s' ->
    exists t', 
      (trans tau)^* t t' /\ R s' t') /\
  (diverges s -> diverges t) /\
  (lock = WSOpt.nolock \/ (is_stuck s -> is_stuck t))
|}.
Next Obligation.
Admitted.

Lemma divsim_equiv :
  forall s t, sim WSOpt.compress_ind WSOpt.nolock WSOpt.expand s t ->
  gfp (divsimF WSOpt.nolock) s t.
Proof.
  coinduction R CH. intros.
  apply (gfp_fp (simF _ _ _)) in H.
  revert CH. (*induction H.*)
  repeat split; intros.
  - admit.
  - admit.
  - change (gfp (simF WSOpt.compress_ind WSOpt.nolock WSOpt.expand)) with (sim WSOpt.compress_ind WSOpt.nolock WSOpt.expand) in H.
    (*revert s t H CH H0. red. coinduction R' CH'.*) (*apply (gfp_fp divergesF).*)
    intros. apply (gfp_fp divergesF) in H0.
    destruct H0 as (? & ? & ?).
    apply H in H0 as [].
    + apply (gfp_fp divergesF). exists t'. split; auto. admit.
    + discriminate.
    + destruct SIM as [SIM _].
      assert (diverges t) by admit. apply H2.
    + assert (diverges t') by admit. admit.
  - auto.
Abort.

Theorem upto_sim_l :
  forall s s' t (Hstuck : extrans s \/ lock = WSOpt.nolock), (* \/ taustar_det t t' *)
  `R s' t ->
  wsim div lock exp ub s s' ->
  `R s t.
Proof.
  apply tower.
  - intros ??????????. red.
    eapply H; eauto.
    apply leq_infx in H2. apply H2, H0.
  - intros. repeat split; intros; subst.
    + apply (gfp_fp (wsimF _ _ _ _)) in H1.
      apply H1 in H2 as (? & ? & ? & ? & ?).
      admit.
    + apply (gfp_fp (wsimF _ _ _ _)) in H1.
      apply H1 in H2 as (? & ? & ?).
      clear H2. assert (H2 : trans tau s' x0) by admit.
      apply H0 in H2 as (? & ? & ?).
      exists x1. split; auto.
      (* problem if H2 is the identity *)
      admit.
Abort.


(*Lemma wsim_obs' :
  forall s t
    (Hstuck : extrans s \/ lock = WSOpt.nolock),
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
Qed.*)

Lemma wsim_obs :
  forall s t
    (Hstuck : extrans s \/ lock = WSOpt.nolock),
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
    (Hstuck : extrans s \/ is_stuck t \/ lock = WSOpt.nolock), (* basically the definition of complete sim *)
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
