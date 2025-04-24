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

Variant label {S : Type} := obs (s : S) | tau.

Record LTS := {
  Observable : Type;
  St : EqType;
  trans : @label Observable -> srel St St;
  epsilon : srel St St;
  Robs : Observable -> Observable -> Prop;
  ub_state : St -> Prop;
}.

(*Section LockLTS.

  Context (lts : LTS).
  Variant LockObservable := | Event (e : lts.(Observable)) | NoEvent.
  Program Definition LockSt := {| type_of := (bool * lts.(St))%type |}.
  Variant locktrans : @label LockObservable -> LockSt -> LockSt -> Prop :=
  | locktrans_ev b o s t : lts.(trans) (obs o) s t -> locktrans (obs (Event o)) (b, s) (true, t)
  | locktrans_noev s : (forall l t, lts.(trans) l s t -> False) -> locktrans (obs NoEvent) (true, s) (true, s)
  .
  Definition lockepsilon : LockSt -> LockSt -> Prop :=
    fun '(b, s) '(b', s') =>
    lts.(epsilon) s s' /\ (
      (b = false /\ b' = false) \/
      (b = true /\ b' = false) \/
      (b = true /\ b' = true /\ forall l s'', lts.(trans) l s s'' -> False)
    ).
  Definition LockRobs : LockObservable -> LockObservable -> Prop. Admitted.
  Definition lock_ub_state : LockSt -> Prop. Admitted.

  Definition lock := {|
    Observable := LockObservable;
    St := LockSt;
    trans := locktrans;
    epsilon := lockepsilon;
    Robs := LockRobs;
    ub_state := lock_ub_state
  |}.

End LockLTS.*)

Section WithLTS.

Context (lts : LTS).
Let Observable := lts.(Observable).
Let St := lts.(St).
Let trans := lts.(trans).
Let epsilon := lts.(epsilon).
Let Robs := lts.(Robs).
Let ub_state := lts.(ub_state).
Let label := @label Observable.

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
#[local] Ltac esim := eauto 10 with optsim exfalso.

Program Definition divergesF : mon (St -> Prop) :=
{| body R st :=
  exists st', trans tau st st' /\ R st'
|}.
Next Obligation.
  eauto.
Qed.

Definition diverges := gfp divergesF.

#[export] Instance : Proper (St.(Eq) ==> flip impl) diverges.
Proof.
Admitted.

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

Context (freeze : SimOpt.freeze_opt) (lock : SimOpt.lock_opt) (delay : SimOpt.delay_opt).

Variant DTauAnswer (R Rind : relation St) s' t : Prop :=
| dtau_match t' (TR : trans tau t t') (DIV : R s' t')
| dtau_div (DIV : Rind s' t)
.
Hint Constructors DTauAnswer : optsim.

#[export] Instance DTauAnswer_eq R Rind :
  Proper (Eq St ==> Eq St ==> impl) R ->
  Proper (Eq St ==> Eq St ==> impl) Rind ->
  Proper (Eq St ==> Eq St ==> impl) (DTauAnswer R Rind).
Proof.
  intros. cbn. intros. destruct H3.
  - rewrite H2 in TR. rewrite H1 in DIV. esim.
  - rewrite H1, H2 in DIV. esim.
Qed.

Definition divpresIndF R Rind s t :=
  forall s', trans tau s s' -> DTauAnswer R Rind s' t.

Section NoElim.
#[local] Unset Elimination Schemes.
Inductive divpresInd R s t : Prop :=
| divpresI : divpresIndF R (divpresInd R) s t -> divpresInd R s t.
End NoElim.

Definition divpresInd_ind :
  forall R P : St -> St -> Prop,
       (forall s t : St,
         (divpresIndF R (fun s t => divpresInd R s t /\ P s t) s t) -> 
        P s t) -> forall t t0 : St, divpresInd R t t0 -> P t t0.
Proof.
  intros until 1. fix F 3. intros. apply H. destruct H0.
  red. intros. apply H0 in H1 as [].
  - eleft; eauto.
  - eright; eauto.
Qed.

Program Definition divpresF : mon (St -> St -> Prop) :=
{| body R s t := divpresInd R s t |}.
Next Obligation.
  induction H0. constructor. intros ??.
  apply H0 in H1 as []. eleft; eauto. eright; eauto. apply DIV.
Qed.

#[export] Instance divpresF_eq R :
  Proper (Eq St ==> Eq St ==> impl) R ->
  Proper (Eq St ==> Eq St ==> impl) (divpresF R).
Proof.
  intro. cbn. intros.
  revert y y0 H0 H1. induction H2. intros. constructor. intros ??.
  rewrite <- H1 in H3.
  apply H0 in H3 as [].
  - rewrite H2 in TR. esim.
  - right. now eapply DIV.
Qed.

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

Section SimInd.

  Variant TauIndAnswer (R Rind : relation St) s' t : Prop :=
  | taui_exact t' (TR : trans tau t t') (SIM : R s' t')
  | taui_freeze (_ : freeze = SimOpt.freeze) (SIM : R s' t)
  | taui_div (_ : freeze = SimOpt.freeze_div) (SIM : Rind s' t)
  | taui_delay t' (_ : delay = SimOpt.delay) (TR : (trans tau)^+ t t') (SIM : R s' t')
  .
  Hint Constructors TauIndAnswer : optsim.

  Definition simIndF R Rind s t :=
    (forall o s', trans (obs o) s s' ->
      ObsAnswer R s' t o
    ) /\
    (forall s', trans tau s s' ->
      TauIndAnswer R Rind s' t
    ) /\
    (lock = SimOpt.nolock \/ (is_stuck s -> is_stuck t)).

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

End SimInd.

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

Lemma simInd_mon : forall R R', R <= R' -> simInd R <= simInd R'.
Proof.
  cbn. intros. induction H0.
  repeat split; intros.
  - apply H0 in H1 as []; esim.
  - apply H0 in H1 as []; esim.
    destruct SIM. esim.
  - apply H0.
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
  (lock = SimOpt.nolock \/ (is_stuck s -> is_stuck t))
|}.
Next Obligation.
  repeat split; intros; auto.
  - apply H0 in H4 as (? & ? & ? & ? & ?). eauto 6.
  - apply H1 in H4 as (? & ? & ?). eauto.
Qed.

Definition divsim := gfp (divsimF SimOpt.nolock).

Program Definition divsimF' : mon (St -> St -> Prop) :=
{|
  body := fun R s t => (forall o s', trans (obs o) s s' ->
    exists o' t',
        ((trans tau)^* ⋅ trans (obs o')) t t' /\
      R s' t' /\
      Robs o o') /\
  (forall s', trans tau s s' ->
    exists t', 
      (trans tau)^* t t' /\ R s' t') /\
  (diverges s -> diverges t)
|}.
Next Obligation.
  repeat split; intros; auto.
  - apply H0 in H3 as (? & ? & ? & ? & ?). eauto 6.
  - apply H1 in H3 as (? & ? & ?). eauto.
Qed.

Definition divsim' := gfp divsimF'.

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

Inductive nodiv s : Prop :=
| nodiv_tau : (forall s', trans tau s s' -> nodiv s') -> nodiv s
.

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

Lemma diverges_nodiv : forall s,
  nodiv s ->
  diverges s ->
  False.
Proof.
  intros. induction H.
  apply (gfp_fp divergesF) in H0 as (? & ? & ?).
  apply H1 in H0 as [].
  apply H2.
Qed.

Lemma diverges_impl_nodiv : forall s t,
  nodiv s \/ diverges t ->
  (diverges s -> diverges t).
Proof.
  intros. destruct H.
  - now apply diverges_nodiv in H; auto.
  - apply H.
Qed.

Definition divpres := gfp divpresF.

Axiom diverges_lem : forall s, diverges s \/ nodiv s.

Lemma divpres_impl : forall s t,
  divpres s t ->
  diverges s -> diverges t.
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp divpresF) in H. induction H. apply (gfp_fp divergesF) in H0 as (? & ? & ?).
  apply H in H0 as [].
  - exists t'. eauto.
  - now apply DIV.
Qed.

Lemma trans_add_delay : forall l,
  trans l ≦ (trans tau)^* ⋅ trans l.
Proof.
  intros. esplit; eauto. now rewrite <- str_refl.
Qed.

Lemma divsim_divpres : forall s t,
  divsim s t ->
  sim false s t.
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp (divsimF _)) in H. destruct H as (_ & _ & ? & _).
  destruct (diverges_lem s).
  apply H in H0. eapply chain_div in H0. apply H0; auto.
  eapply chain_nodiv with (R := R) (t := t) in H0. apply H0; auto.
Qed.

(* ok *)
Lemma divsim_equiv
  (Hfreeze : freeze = SimOpt.freeze_div)
  (Hlock : lock = SimOpt.nolock)
  (Hdelay : delay = SimOpt.delay) :
  forall b s t, divsim s t ->
  sim b s t.
Proof.
  red. coinduction R CH. intros. destruct b.
  2: now apply (gfp_bchain R), divsim_divpres.
  constructor.
  repeat split; intros.
  - apply (gfp_fp (divsimF _)) in H. destruct H as (? & ? & _).
    apply trans_add_delay in H0.
    apply H in H0 as (? & ? & ? & ? & ?).
    eapply ans_delay_obs; eauto.
  - apply (gfp_fp (divsimF _)) in H.
    rewrite (str_ext (trans tau)) in H0.
    apply H in H0 as (? & ? & ?).
    rewrite str_itr in H0. destruct H0.
    + apply tau_div. assumption. apply CH. cbn in H0. admit.
      apply CH. admit.
    + eapply tau_delay; eauto.
  - now left.
Admitted.

Lemma divpresF_tau_r : forall (R : Chain simF) s t t',
  `R false s t' ->
  trans tau t t' ->
  `R false s t.
Proof.
  intro. apply tower. {
    intros ?????????. eapply H; eauto.
  }
  clear R. intros R **.
  apply simF_equiv in H0. induction H0.
  do 2 constructor. intros ??.
  apply H0 in H2 as [].
  - esim.
  - apply dtau_div. apply simF_equiv. now apply DIV.
Qed.

Lemma divpresF_taustar_r : forall (R : Chain simF) s t t',
  `R false s t' ->
  (trans tau)^* t t' ->
  `R false s t.
Proof.
Admitted.

Lemma dtau_plus : forall (R : Chain simF) Rind s' t t',
  (trans tau)^+ t t' ->
  `R false s' t' ->
  DTauAnswer (` R false) Rind s' t.
Proof.
  intros.
  rewrite itr_str_l in H. destruct H.
  eapply dtau_match. apply H.
  eapply divpresF_taustar_r; eauto.
Qed.
Hint Resolve dtau_plus : optsim.

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

Lemma divsim_equiv'
  (Hfreeze : freeze = SimOpt.freeze_div)
  (Hlock : lock = SimOpt.nolock)
  (Hdelay : delay = SimOpt.delay) :
  forall s t, (forall b, sim b s t) ->
  divsim' s t.
Proof.
  red. coinduction R CH. intros. cbn -[dot str]. repeat split; intros.
  - specialize (H true). apply sim_fp in H. apply H in H0 as []; auto.
    + exists o', t'. split. { now apply trans_add_delay. }
      split; auto. apply CH. intros. destruct b; auto.
      now apply sim_f_t.
    + exists o', t'. repeat split; auto.
      apply CH. intros. destruct b; auto. now apply sim_f_t.
  - specialize (H true). apply sim_fp in H. apply H in H0 as []; auto.
    + exists t'. split. { now rewrite <- str_ext. }
      apply CH. intros []; auto. now apply sim_f_t.
    + now rewrite Hfreeze in H0.
    + exists t. split. { now rewrite <- str_refl. }
      apply CH. intros []; try easy.
    + exists t'. split. { now rewrite <- str_itr'. }
      apply CH. intros []; auto. now apply sim_f_t.
  - specialize (H false). revert s t H H0. clear R CH. red. coinduction R CH. intros.
    cbn. apply sim_fp in H. revert H0. induction H. intros.
    apply (gfp_fp divergesF) in H0 as (? & ? & ?). apply H in H0. destruct H0; eauto.
    destruct DIV. apply H2 in H1 as (? & ? & ?). eauto.
Qed.

Lemma sim_tau_l (R : Chain simF) (Hfreeze : freeze = SimOpt.freeze_div) :
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

Section SimUpTo.

Context (*(div : SimOpt.div_opt) (lock : SimOpt.lock_opt)
  (exp : SimOpt.exp_opt) (ub : SimOpt.ub_opt)*)
  (R : Chain simF).

(*Definition upto_refl `{Reflexive _ Robs} :
  Reflexive `R.
Proof.
  apply tower.
  - firstorder.
  - repeat split; intros; auto.
    + eauto 8 with optsim.
    + eauto with optsim.
Qed.*)

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

#[export] Instance simF_eq' R :
  Proper (eq ==> Eq St ==> Eq St ==> impl) R ->
  Proper (eq ==> Eq St ==> Eq St ==> iff) (simF R).
Proof.
  split; subst; eapply simF_eq; eauto; now symmetry.
Qed.

Theorem sim_inv_taustar_l :
  forall (Hdelay : delay = SimOpt.delay) s s' t,
  (trans tau)^* s s' ->
  sim true s t ->
  sim true s' t.
Proof.
  intros. revert H0.
  eapply srel_str_ind_l' with (i := trans tau) (P := fun s s' => sim true s t -> sim true s' t); auto.
  - cbn. intros. Set  Typeclasses Depth 10. now rewrite H0, H1.
  - intros. rewrite <- H0. apply H1.
  - intros. apply H1. eapply sim_inv_tau_l; eauto.
Qed.

Lemma divergesF_taustar : forall (R : Chain divergesF) s s',
  (trans tau)^* s s' ->
  `R s' ->
  `R s.
Proof.
  intro. apply tower. {
    intros ????????. eapply H; eauto.
  }
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


Lemma sim_diverges : forall (Hfreeze : freeze = SimOpt.freeze_div) s t,
  sim true s t ->
  diverges s ->
  diverges t.
Proof.
  intros. eapply divpres_impl; eauto. Fail eapply sim_divpres; eauto.
Admitted.

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

Lemma diverges_divpres :
  forall s t, diverges t -> divpres s t.
Proof.
  red. coinduction R CH.
  intros. constructor. intros ??.
  apply (gfp_fp divergesF) in H as (? & ? & ?).
  eleft; eauto.
Qed.

Lemma divpres_trans_l : forall (R : Chain simF) s t u,
  `R false t u ->
  divpres s t ->
  `R false s u.
Proof.
  intros ?. apply tower. {
    intros ?????????. eapply H; eauto.
  }
  clear R. intros R **.
  apply simF_equiv in H0.
  revert s H1. induction H0. rename t into u. rename s into t. intros.
  apply (gfp_fp divpresF) in H1. induction H1.
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
Hint Constructors DTauAnswer : optsim.
Hint Resolve dtau_plus : optsim.
Hint Resolve simF_false : optsim.
Hint Resolve simF_true : optsim.

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
      eapply divpres_trans_l with (t := t'). apply DIV. admit.
    + (* tau_freeze *) subst freeze.
      eapply tau_freeze; eauto. eapply H; eauto. apply (b_chain x). apply simF_equiv. apply H0.
    + (* tau_div *) subst freeze.
      eapply tau_div; eauto with optsim.
      eapply H; eauto. apply (b_chain x). apply simF_equiv. apply H0.
      apply simF_equiv in H0; auto. eapply simF_f_t in H0. 2: discriminate.
      apply divpres_trans_l with (s := s'0) in H0; auto. admit.
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
