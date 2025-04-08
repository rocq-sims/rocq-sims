From Coq Require Import Init Program.Equality.
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

Create HintDb optsim.
#[local] Ltac esim := eauto 10 with optsim.

(*
#[export] Instance Transitive_taustar : Transitive taustar.
Proof.
  red. intros. induction H; auto.
  apply IHtaustar in H0.
  eright; eauto.
Qed.
*)

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

Variant extrans (st : St) : Prop :=
trans_intro l st' : trans l st st' -> extrans st.
Hint Constructors extrans : optsim.

#[export] Instance : Proper (St.(Eq) ==> flip impl) extrans.
Proof.
  cbn. intros ??? []. rewrite <- H in H0. eauto with optsim.
Qed.

Definition is_stuck (st : St) : Prop :=
  ~ extrans st.

#[export] Instance : Proper (St.(Eq) ==> flip impl) is_stuck.
Proof.
  cbn. unfold is_stuck. intros. now setoid_rewrite H.
Qed.

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
| ans_expand l' t' (_ : expand = WSOpt.expand) (TR : ((trans tau)^+ ⋅ trans l') t t') (SIM : R s' t') (LBL : RL l l')
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
  (forall o s', trans (obs o) s s' -> ObsAnswer R s' t o) /\
  (forall s', trans tau s s' -> TauAnswer R Rind s' t) /\
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

Lemma itr_unfold_l `{laws} `{KA ≪ l} :
  forall (n : ob X) (x : X n n), x^+ ≡ x + x⋅x^+.
Proof.
  intros. now rewrite itr_str_l, str_unfold_l, <- itr_str_l, dotxpls, dotx1 at 1.
Qed.

Lemma itr_unfold_r `{laws} `{KA ≪ l} :
  forall (n : ob X) (x : X n n), x^+ ≡ x + x^+⋅x.
Proof.
  intros. now rewrite itr_str_r, kleene.str_unfold_r, <- itr_str_r, dotplsx, dot1x at 1.
Qed.

Lemma str_itr' `{laws} `{KA ≪ l} :
  forall (n : ob X) (x : X n n), x^+ ≦ x^*.
Proof.
  intros. now rewrite str_itr, <- leq_cup_r.
Qed.

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
    intro. apply H3. econstructor; eapply H2.
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
    (Hexpand : expand = WSOpt.expand),
  trans tau s s' ->
  simF `R s t ->
  `R s' t.
Proof.
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

Theorem sim_tau_r :
  forall compress lock s t t'
    (Hstuck : extrans s \/ lock = WSOpt.nolock) (* \/ taustar_det t t' *),
  (trans tau)^* t t' ->
  sim compress lock WSOpt.expand s t' ->
  sim compress lock WSOpt.expand s t.
Proof.
  unfold sim. intros ??. apply gfp_prop.
  intros. eapply upto_tau_r; eauto. apply WSOpt.noub.
Qed.

Theorem sim_inv_tau_l :
  forall compress lock s s' t,
  trans tau s s' ->
  sim compress lock WSOpt.expand s t ->
  sim compress lock WSOpt.expand s' t.
Proof.
  unfold sim. intros. apply (gfp_fp (simF _ _ _)) in H0. revert H0. eapply gfp_prop.
  intros. eapply inv_tau_l; eauto. constructor.
Qed.

Lemma srel_str_ind_l' {E : EqType} :
  forall (i : srel E E) (P : E -> E -> Prop),
  Proper (E.(Eq) ==> E.(Eq) ==> iff) P ->
  (forall s t, E.(Eq) s t -> P s t) ->
  (forall s t u, i s t -> P t u -> P s u) ->
  forall s t, i^* s t -> P s t.
Proof.
  intros.
  eset (P' := {| hrel_of := fun s t => P s t|} : srel E E).
  epose proof (str_ind_l1 (X := srel_monoid_ops)). specialize (H3 E i P'). cbn in H3. eapply H3.
  - intros. now apply H0.
  - intros. red in H4. destruct H4. eapply H1; eauto.
  - apply H2.
Qed.

Theorem sim_inv_taustar_l :
  forall compress lock s s' t,
  (trans tau)^* s s' ->
  sim compress lock WSOpt.expand s t ->
  sim compress lock WSOpt.expand s' t.
Proof.
  intros. revert H0.
  eapply srel_str_ind_l' with (i := trans tau) (P := fun s s' => sim _ _ _ s t -> sim _ _ _ s' t); auto.
  - cbn. intros. now rewrite H0, H1.
  - intros. rewrite <- H0. apply H1.
  - intros. apply H1. eapply sim_inv_tau_l; eauto.
Qed.

Lemma srel_str_ind_l {E : EqType} :
  forall (P : E -> Prop) (i : srel E E),
  Proper (E.(Eq) ==> iff) P ->
  (forall s t : E, i s t -> P t -> P s) ->
  forall s t : E, i^* s t -> P t -> P s.
Proof.
  intros.
  eset (P' := {| hrel_of := fun s t => P t -> P s|} : srel E E).
  epose proof (str_ind_l1 (X := srel_monoid_ops)). specialize (H3 E i P'). cbn in H3. eapply H3.
  - intros. now rewrite H4.
  - intros. red in H4. destruct H4. eauto.
  - apply H1.
  - apply H2.
  Unshelve.
  cbn. intros. now rewrite H3, H4.
Qed.

Lemma srel_str_ind_r {E : EqType} :
  forall (P : E -> Prop) (i : srel E E),
  Proper (E.(Eq) ==> iff) P ->
  (forall s t : E, i s t -> P s -> P t) ->
  forall s t : E, i^* s t -> P s -> P t.
Proof.
  intros.
  eset (P' := {| hrel_of := fun s t => P s -> P t|} : srel E E).
  epose proof (str_ind_r1 (X := srel_monoid_ops)). specialize (H3 E i P'). cbn in H3. eapply H3.
  - intros. now rewrite <- H4.
  - intros. red in H4. destruct H4. eapply H0; eauto.
  - apply H1.
  - apply H2.
  Unshelve.
  cbn. intros. now rewrite H3, H4.
Qed.


Lemma divergesF_taustar : forall (R : Chain divergesF) s s',
  (trans tau)^* s s' ->
  `R s' ->
  `R s.
Proof.
  intro. apply tower. admit.
  intros. rewrite str_itr in H0. destruct H0.
  - admit.
  - rewrite itr_str_l in H0. destruct H0.
    exists x0. split; auto. eapply H. apply H2.
    now apply (b_chain x).
Admitted.

Lemma divergesF_tauplus : forall (R : Chain divergesF) s s',
  (trans tau)^+ s s' ->
  `R s' ->
  divergesF `R s.
Proof.
  intros. rewrite itr_str_l in H. destruct H.
  exists x. split; auto. eapply divergesF_taustar; eauto.
Qed.

Lemma diverges_tauplus : forall s s',
  (trans tau)^+ s s' ->
  diverges s' ->
  diverges s.
Proof.
  unfold diverges. apply gfp_prop.
  intros. apply (b_chain x). eapply divergesF_tauplus; eauto.
Qed.


Lemma sim_diverges : forall lock expand s t,
  sim WSOpt.compress_ind lock expand s t ->
  diverges s ->
  diverges t.
Proof.
  red. coinduction R CH.
  intros. apply (gfp_fp (simF _ _ _)) in H. revert H0. induction H.
  intros.
  apply (gfp_fp divergesF) in H0 as (? & ? & ?).
  apply H in H0. destruct H0.
  - exists t'; split; eauto.
  - discriminate.
  - destruct SIM. eauto.
  - eapply divergesF_tauplus; eauto.
Qed.

Hint Constructors ObsAnswer : optsim.
Hint Constructors TauAnswer : optsim.

Lemma sim_tau_weak :
  forall compress lock expand (Hcompress : compress <> WSOpt.compress_ind) s s' t R,
  simF compress lock expand R s t ->
  trans tau s s' ->
  exists t', (trans tau)^* t t' /\ R s' t'.
Proof.
  intros. apply H in H0 as [].
  - exists t'. split; auto. now rewrite <- str_ext.
  - exists t. split; auto. now rewrite <- str_refl.
  - easy.
  - exists t'. split; auto. now rewrite <- str_itr'.
Qed.

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
  intros. revert t H1. induction H0.
  repeat split; intros; subst.
  - apply H0 in H2 as [].
    + apply (gfp_fp (simF _ _ _)) in H1. destruct H1.
      apply H1 in TR. destruct TR; eauto with optsim.
    + destruct TR as [t'' TR1 TR2].
      subst. eapply sim_inv_taustar_l in H1; eauto.
      apply (gfp_fp (simF _ _ _)) in H1.
      apply H1 in TR2. destruct TR2; eauto with optsim.
  - apply H0 in H2 as [].
    + (* tau_exact *) apply (gfp_fp (simF _ _ _)) in H1. destruct H1.
      apply H1 in TR as ?. destruct H2; eauto with optsim.
      * (* compress_coind *) destruct compress; try discriminate. apply tau_compress; auto. eapply H; eauto.
      * (* compress_ind *) destruct compress; discriminate.
    + (* tau_compress *) subst compress.
      eapply tau_compress; eauto.
    + (* tau_div *) subst compress.
      eapply tau_div; auto.
      now apply SIM.
    + (* tau_expand *)
      rewrite itr_str_r in TR. destruct TR as [t'1 TR1 TR2].
      subst.
      eapply sim_inv_taustar_l in H1; eauto.
      apply (gfp_fp (simF _ _ _)) in H1.
      apply H1 in TR2.
      destruct compress; destruct TR2; try discriminate; eauto with optsim.
  - destruct H0. apply (gfp_fp (simF _ _ _)) in H1 as [(_ & _ & ?)]. intuition.
Qed.

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
  repeat split; intros; auto.
  - apply H0 in H4 as (? & ? & ? & ? & ?). eauto 6.
  - apply H1 in H4 as (? & ? & ?). eauto.
Qed.

Lemma divsim_equiv :
  forall s t, sim WSOpt.compress_ind WSOpt.nolock WSOpt.expand s t ->
  gfp (divsimF WSOpt.nolock) s t.
Proof.
  intros. apply (gfp_fp (divsimF _)).
  repeat split; intros.
  - admit.
  - admit.
  - intros. now apply sim_diverges in H.
  - auto.
Admitted.

(*Theorem upto_sim_l :
  forall s s' t (Hstuck : extrans s \/ lock = WSOpt.nolock),
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


Lemma wsim_obs' :
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
Qed.

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
*)
