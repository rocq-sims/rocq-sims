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

Module SimOpt.

  Variant compress_opt := compress_mut | compress_coind | nocompress.
  Definition div := compress_mut.
  Variant lock_opt := lock | nolock.
  Variant expand_opt := expand | noexpand.
  Variant ub_opt := noub | ub | ttub. (* TODO can non-TT UB be characterized just as "every transition is possible"? *)

End SimOpt.

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
#[local] Ltac esim := eauto 10 with optsim.

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

Context (compress : SimOpt.compress_opt)
  (lock : SimOpt.lock_opt)
  (expand : SimOpt.expand_opt)
  (ub : SimOpt.ub_opt).

Variant DTauAnswer (R Rind : relation St) s' t : Prop :=
| dtau_match t' (TR : trans tau t t') (DIV : R s' t')
| dtau_div (DIV : Rind s' t)
.

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

Variant ObsAnswer (R : relation St) s' t o : Prop :=
| ans_obs o' t' (TR : trans (obs o') t t') (SIM : R s' t') (OBS : Robs o o') : ObsAnswer R s' t o
| ans_delay_obs o' t' (_ : expand = SimOpt.expand) (TR : ((trans tau)^* ⋅ trans (obs o')) t t') (SIM : R s' t') (OBS : Robs o o') : ObsAnswer R s' t o
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
Variant TauAnswer (R : relation St) Rdiv s' t : Prop :=
| tau_exact t' (TR : trans tau t t') (SIM : R s' t')
| tau_compress (_ : compress = SimOpt.compress_coind) (SIM : R s' t)
| tau_div (_ : compress = SimOpt.compress_mut) (SIM : R s' t) (DIV : divpresF Rdiv s' t)
| tau_expand t' (_ : expand = SimOpt.expand) (TR : (trans tau)^+ t t') (SIM : R s' t')
.
Hint Constructors TauAnswer : optsim.

#[export] Instance : forall R Rdiv,
  Proper (St.(Eq) ==> St.(Eq) ==> iff) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> iff) Rdiv ->
  Proper (St.(Eq) ==> St.(Eq) ==> flip impl) (TauAnswer R Rdiv).
Proof.
  intros. cbn. intros.
  destruct H3; rewrite <- ?H1, <- ?H2 in *; eauto with optsim.
Admitted.

Lemma tau_weak :
  compress = SimOpt.compress_coind ->
  expand = SimOpt.expand ->
  forall R Rdiv s' t t',
  Proper (St.(Eq) ==> St.(Eq) ==> iff) R ->
  (trans tau)^* t t' -> R s' t' -> TauAnswer R Rdiv s' t.
Proof.
  intros -> -> * ? TR SIM.
  rewrite str_itr in TR. destruct TR as [TR | TR].
  - cbn in TR. apply tau_compress; auto. now rewrite TR.
  - eapply tau_expand; eauto.
Qed.

Lemma tau_weak_div :
  compress = SimOpt.compress_mut ->
  expand = SimOpt.expand ->
  forall R Rdiv s' t t',
  Proper (St.(Eq) ==> St.(Eq) ==> iff) R ->
  Proper (St.(Eq) ==> St.(Eq) ==> iff) Rdiv ->
  (trans tau)^* t t' -> R s' t' -> divpresF Rdiv s' t' -> TauAnswer R Rdiv s' t.
Proof.
  intros -> -> * ?? TR SIM DIV.
  rewrite str_itr in TR. destruct TR as [TR | TR].
  - cbn in TR. apply tau_div; auto. now rewrite TR. admit.
  - eapply tau_expand; eauto.
Admitted.

Definition RL l l' :=
  match l, l' with
  | tau, tau => True
  | obs o, obs o' => Robs o o'
  | _, _ => False
  end.

Section SimInd.

  Variant TauIndAnswer (R Rind : relation St) s' t : Prop :=
  | taui_exact t' (TR : trans tau t t') (SIM : R s' t')
  | taui_compress (_ : compress = SimOpt.compress_coind) (SIM : R s' t)
  | taui_div (_ : compress = SimOpt.compress_mut) (SIM : Rind s' t)
  | taui_expand t' (_ : expand = SimOpt.expand) (TR : (trans tau)^+ t t') (SIM : R s' t')
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
| ans_compress (_ : compress = SimOpt.compress_coind) (SIM : R s' t) (LBL : l = tau)
| ans_div (_ : compress = SimOpt.compress_ind) (SIM : Rind s' t) (LBL : l = tau)
| ans_expand l' t' (_ : expand = SimOpt.expand) (TR : ((trans tau)^+ ⋅ trans l') t t') (SIM : R s' t') (LBL : RL l l')
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

Program Definition simF :
  mon (bool -> St -> St -> Prop) :=
{| body R b s t :=
  (b = false -> divpresF (R false) s t) /\
  (b = true -> (forall o s', trans (obs o) s s' -> ObsAnswer (R true) s' t o) /\
  (forall s', trans tau s s' -> TauAnswer (R true) (R false) s' t) /\
  (lock = SimOpt.nolock \/ (is_stuck s -> is_stuck t)) (* FIXME tau* in answer *))
|}.
Next Obligation.
  repeat split; intros.
  - eapply (Hbody divpresF). 2: { apply H0. auto. } cbn. intros. now apply H.
  - apply H1 in H3 as []; esim.
  - apply H1 in H3 as []; esim. admit.
  - now apply H1.
Admitted.

#[export] Instance simF_eq R :
  Proper (eq ==> Eq St ==> Eq St ==> iff) R ->
  Proper (eq ==> Eq St ==> Eq St ==> flip impl) (simF R).
Proof.
  intros. cbn. intros. subst. destruct H3, y; split; intro; try discriminate.
  - specialize (H3 eq_refl). destruct H3 as (? & ? & ?).
    repeat split; intros; rewrite ?H1, ?H2 in * |- *; auto.
  - admit.
Admitted.

#[export] Instance Chain_simF_eq : forall (R : Chain simF),
  Proper (eq ==> Eq St ==> Eq St ==> iff) ` R.
Proof.
  intro. apply tower. {
    intros ? INC ?? <- ??????. split; intros ???.
    - eapply INC. assumption. reflexivity.
      now rewrite <- H. now rewrite <- H0.
      now apply H1.
    - eapply INC. assumption. reflexivity.
      now rewrite H. now rewrite H0.
      now apply H1.
  }
  intros. split; intro; subst.
  now rewrite H1, H2 in H3.
  now rewrite H1, H2.
Qed.

Definition sim := gfp simF.

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
  clear R. intros R **.
  cbn. split; intros; try discriminate.
  clear H1. constructor. intros ??.
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
  cbn. split; intros; try discriminate.
  clear H1.
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

(*Program Definition divpresF' : mon (St -> St -> Prop) :=
{| body R s t :=
  (forall s', trans tau s s' -> exists t', (trans tau)^+ t t' /\ R s' t') \/ nodiv s
|}.
Next Obligation.
Admitted.

Definition divpres' := gfp divpresF'.

Lemma divpres'_divpres : forall s t, divpres' s t -> divpres s t.
Proof.
(*  red. coinduction R CH. intros.
  apply (gfp_fp divpresF') in H.
  constructor. intros ??.
  apply H in H0 as [].
  - destruct H0 as (? & ? & ?). admit.
  - (* chain_nodiv *) admit.*)
Admitted.
(* dans l'autre sens ça va encore mal se passer *)

Lemma divpres'_tau_r : forall (R : Chain divpresF') s t t',
  trans tau t t' ->
  `R s t' ->
  `R s t.
Proof.
(*  intro. apply tower. admit. clear R. intros R ** ??.
  apply H1 in H2 as [].
  - left. destruct H2 as (? & ? & ?).
    exists x. admit.
  - right. apply H2.*)
Admitted.*)

(*Axiom extau_dec : forall s,
  ((exists s', trans tau s s') \/ forall s', ~ trans tau s s').*)

(*Lemma divpres_divpres' : forall s t, divpres s t -> divpres' s t.
Proof.
  red. coinduction R CH. intros.
  apply (gfp_fp divpresF) in H. induction H.
  intros ??. apply H in H0 as [].
  - left. exists t'. split; auto. admit.
  - unfold divpresF' in DIV. cbn in DIV. apply DIV.
Abort.*)

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

(* ok *)
Lemma divsim_equiv
  (Hcompress : compress = SimOpt.compress_mut)
  (Hlock : lock = SimOpt.nolock)
  (Hexpand : expand = SimOpt.expand) :
  forall b s t, divsim s t ->
  sim b s t.
Proof.
  red. coinduction R CH. intros. cbn. split; intros; try discriminate.
  { apply (gfp_fp (divsimF _)) in H. destruct H as (_ & _ & ? & _).
    destruct (diverges_lem s).
    apply H in H1. eapply chain_div in H1. apply H1; auto.
    eapply chain_nodiv with (R := R) (t := t) in H1. apply H1; auto.

  }
  clear H0.
  repeat split; intros.
  - apply (gfp_fp (divsimF _)) in H. destruct H as (? & ? & _).
    clear H0. assert (((trans tau)^* ⋅ trans (obs o)) s s') by admit.
    apply H in H0 as (? & ? & ? & ? & ?).
    eapply ans_delay_obs; eauto.
  - apply (gfp_fp (divsimF _)) in H.
    clear H0. assert ((trans tau)^* s s') by admit.
    apply H in H0 as (? & ? & ?).
    rewrite str_itr in H0. destruct H0.
    + apply tau_div. assumption. apply CH. cbn in H0. admit.
      admit.
    + eapply tau_expand; eauto.
  - admit.
Admitted.

Lemma sim_divpres : forall s t (Hcompress : compress = SimOpt.compress_mut),
  sim true s t ->
  gfp divpresF s t.
Proof.
  coinduction R CH. intros.
  apply (gfp_fp simF) in H. destruct H as [_ ?]. specialize (H eq_refl).
  constructor. red. intros.
  apply H in H0 as [].
  - eapply dtau_match; eauto.
  - now rewrite Hcompress in H0.
  - apply dtau_div. clear DIV. assert (DIV : gfp divpresF s' t) by admit. apply (gfp_bchain R) in DIV. apply DIV; auto.
  - admit.
Admitted.

Lemma sim_f_t : forall s t (Hcompress : compress = SimOpt.compress_mut),
  sim true s t ->
  sim false s t.
Proof.
  red. coinduction R CH. intros.
  split; intros; try discriminate. clear H0.
  apply (gfp_fp simF) in H. destruct H as [_ ?]. specialize (H eq_refl).
  constructor. red. intros.
  apply H in H0 as [].
  - eapply dtau_match; eauto.
  - now rewrite Hcompress in H0.
  - apply dtau_div. (*apply (gfp_bchain R) in DIV. apply DIV; auto.*) admit.
  - admit.
Admitted.

Lemma simF_f_t : forall (R : Chain simF) s t (Hcompress : compress = SimOpt.compress_mut),
  simF `R true s t ->
  simF `R false s t.
Proof.
  intro. apply tower. {
    intros ????????. apply H; auto.
  }
  clear R. intros R **.
  split; intros; try discriminate. clear H1.
  destruct H0 as [_ ?]. specialize (H0 eq_refl).
  constructor. red. intros.
  apply H0 in H1 as [].
  - eapply dtau_match; eauto.
  - now rewrite Hcompress in H1.
  - apply dtau_div. apply DIV.
  - admit.
Admitted.

Lemma divsim_equiv'
  (Hcompress : compress = SimOpt.compress_mut)
  (Hlock : lock = SimOpt.nolock)
  (Hexpand : expand = SimOpt.expand) :
  forall s t, (forall b, sim b s t) ->
  divsim' s t.
Proof.
  red. coinduction R CH. intros. cbn -[dot str]. repeat split; intros.
  - specialize (H true). apply (gfp_fp simF) in H. apply H in H0 as []; auto.
    + exists o', t'. split. admit. split; auto. apply CH. intros. destruct b; auto.
      now apply sim_f_t.
    + admit.
  - specialize (H true). apply (gfp_fp simF) in H. apply H in H0 as []; auto.
    + exists t'. split. admit. apply CH. intros. destruct b; auto. now apply sim_f_t.
    + now rewrite Hcompress in H0.
    + exists t. split. admit. apply CH. intros []; try easy. admit.
    + admit.
  - specialize (H false). revert s t H H0. clear R CH. red. coinduction R CH. intros.
    cbn. apply (gfp_fp simF) in H. pose proof (proj1 H eq_refl). clear H. revert H0. induction H1. intros.
    apply (gfp_fp divergesF) in H0 as (? & ? & ?). apply H in H0. destruct H0; eauto.
    destruct DIV. apply H2 in H1 as (? & ? & ?). eauto.
Admitted.

Lemma sim_tau_l (R : Chain simF) (Hcompress : compress = SimOpt.compress_mut) : forall s t,
  is_tau_state s ->
  (forall s', trans tau s s' -> `R true s' t) ->
  `R true s t.
Proof.
  apply tower. {
    intros ????????. apply H; auto.
    intros. apply H1; auto.
  }
  clear R. intros R **.
  split; intro; try discriminate; clear H2.
  - repeat split; intros. 3: admit.
    + now apply H0 in H2.
    + apply H1 in H2. apply tau_div; auto. apply (b_chain R). apply H2.
      apply simF_f_t; auto.
Admitted.

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
    (Hcompress : compress = SimOpt.compress_coind),
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
    * now rewrite Hcompress in H3.
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
    * apply tau_compress; auto. eapply H; eauto.
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
    (Hstuck : extrans s \/ lock = SimOpt.nolock) (* \/ taustar_det t t' *)
    (Hexpand : expand = SimOpt.expand),
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
  intros.
  split; intros; try discriminate. clear H2.
  repeat split; intros; subst.
  + (* observable event *)
    destruct H1 as [_ ?]. specialize (H1 eq_refl). apply H1 in H2 as [].
    * eright; eauto. esplit; eauto.
    * eright; auto. 2: apply SIM. 2: apply OBS. destruct TR. esplit. 2: apply H4.
      rewrite <- str_trans. esplit; eassumption.
  + (* tau *)
    destruct H1 as [_ ?]. specialize (H1 eq_refl). apply H1 in H2 as [].
    * econstructor 4; eauto.
      rewrite itr_str_r. esplit; eauto.
    * (*eapply tau_weak; eauto with optsim. typeclasses eauto.*) admit.
    * eapply tau_weak_div; eauto with optsim.
      epose proof simF_eq.
      assert (forall R : bool -> St -> St -> Prop,
      Proper (eq ==> Eq St ==> Eq St ==> iff) R ->
      Proper (eq ==> Eq St ==> Eq St ==> impl) (simF R)) by admit.
      apply proper_sym_impl_iff_2; try typeclasses eauto. admit. admit.
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
    (Hexpand : expand = SimOpt.expand),
  trans tau s s' ->
  simF `R true s t ->
  `R true s' t.
Proof.
  (*intros. apply sim_alt_equiv in H0.
  destruct H0 as [SIM STUCK].
  apply SIM in H as [].
  - eapply upto_tau_r; eauto. admit. now rewrite <- str_ext.
  - apply SIM0.
  - step. apply SIM0.
  - eapply upto_tau_r; eauto. admit. rewrite str_itr. now right.*)
  (* FIXME check *)
Admitted.

End SimUpTo.
End SimDef.

Theorem sim_tau_r :
  forall compress lock ub s t t'
    (Hstuck : extrans s \/ lock = SimOpt.nolock) (* \/ taustar_det t t' *),
  (trans tau)^* t t' ->
  sim compress lock SimOpt.expand ub true s t' ->
  sim compress lock SimOpt.expand ub true s t.
Proof.
  unfold sim. intros ???. apply gfp_prop.
  intros. eapply upto_tau_r; eauto.
Qed.

Theorem sim_inv_tau_l :
  forall compress lock ub s s' t,
  trans tau s s' ->
  sim compress lock SimOpt.expand ub true s t ->
  sim compress lock SimOpt.expand ub true s' t.
Proof.
  unfold sim. intros. apply (gfp_fp (simF _ _ _ _)) in H0. revert H0. eapply gfp_prop.
  intros. eapply inv_tau_l; eauto.
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
  forall compress lock ub s s' t,
  (trans tau)^* s s' ->
  sim compress lock SimOpt.expand ub true s t ->
  sim compress lock SimOpt.expand ub true s' t.
Proof.
  intros. revert H0.
  eapply srel_str_ind_l' with (i := trans tau) (P := fun s s' => sim _ _ _ _ true s t -> sim _ _ _ _ true s' t); auto.
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


Lemma sim_diverges : forall lock expand ub s t,
  sim SimOpt.compress_mut lock expand ub true s t ->
  diverges s ->
  diverges t.
Proof.
  intros. eapply divpres_impl; eauto. eapply sim_divpres; eauto.
Qed.

Lemma sim_tau_weak :
  forall compress lock expand ub s s' t R,
  simF compress lock expand ub R true s t ->
  trans tau s s' ->
  exists t', (trans tau)^* t t' /\ R true s' t'.
Proof.
  intros. apply H in H0 as []; auto.
  - exists t'. split; auto. now rewrite <- str_ext.
  - exists t. split; auto. now rewrite <- str_refl.
  - exists t. split; auto. now rewrite <- str_refl.
  - exists t'. split; auto. now rewrite <- str_itr'.
Qed.

Hint Constructors ObsAnswer : optsim.
Hint Constructors TauAnswer : optsim.

Lemma diverges_divpres :
  forall s t, diverges t -> divpres s t.
Proof.
  red. coinduction R CH.
  intros. constructor. intros ??.
  apply (gfp_fp divergesF) in H as (? & ? & ?).
  eleft; eauto.
Qed.

Lemma divpres_nocompress_r : forall lock expand ub (R : Chain (simF SimOpt.compress_mut lock expand ub)) s t u,
  `R false s t ->
  sim SimOpt.nocompress lock expand ub true t u ->
  `R false s u.
Proof.
  intros ????. apply tower. {
    intros ?????????. eapply H; eauto.
  }
  clear R. intros R **.
  destruct H0 as [? _]. specialize (H0 eq_refl). induction H0. constructor. intros _. constructor. intros ??. apply H0 in H2 as [].
  - apply (gfp_fp (simF _ _ _ _)) in H1. apply H1 in TR as []; auto.
    + eleft. apply TR. eapply H. apply DIV. apply SIM.
    + discriminate.
    + discriminate.
    + subst. admit.
  - right. apply DIV in H1. apply H1; auto.
Admitted.

Lemma divpres_trans_l : forall compress lock expand ub (R : Chain (simF compress lock expand ub)) s t u,
  `R false t u ->
  divpres s t ->
  `R false s u.
Proof.
  intros ?????. apply tower. {
    intros ?????????. eapply H; eauto.
  }
  clear R. intros R **.
  destruct H0 as [? _]. specialize (H0 eq_refl).
  revert s H1. induction H0. rename t into u. rename s into t. intros.
  apply (gfp_fp divpresF) in H1. induction H1.
  constructor; intros; try discriminate. clear H2. constructor. intros ??.
  apply H1 in H2 as ?. destruct H3.
  - apply H0 in TR. destruct TR.
    + rename t'0 into u'. eapply dtau_match; eauto.
    + apply dtau_div. apply DIV0 in DIV. apply DIV; auto.
  - apply dtau_div. apply DIV; auto.
Qed.

Theorem upto_sim_r :
  forall compress lock expand ub (R : Chain (simF compress lock expand ub)) s t t'
    (OBS : Transitive Robs),
  `R true s t' ->
  sim (match compress with SimOpt.compress_mut => SimOpt.nocompress | _ => compress end) lock expand ub true t' t ->
  `R true s t.
Proof.
  intros ?????.
  apply tower. {
    intros ??????????. red.
    eapply H; eauto.
    apply leq_infx in H2. apply H2, H0.
  }
  intros.
  split; intros; try discriminate. clear H2.
  repeat split; intros; subst.
  - apply H0 in H2 as []; auto.
    + apply (gfp_fp (simF _ _ _ _)) in H1. destruct H1 as [_ ?]. specialize (H1 eq_refl).
      apply H1 in TR. destruct TR; eauto with optsim.
    + destruct TR as [t'' TR1 TR2].
      subst. eapply sim_inv_taustar_l in H1; eauto.
      apply (gfp_fp (simF _ _ _ _)) in H1.
      apply H1 in TR2; auto. destruct TR2; eauto with optsim.
  - apply H0 in H2 as []; auto.
    + (* tau_exact *) apply (gfp_fp (simF _ _ _ _)) in H1. destruct H1 as [_ ?]. specialize (H1 eq_refl).
      apply H1 in TR as ?. destruct H2; eauto with optsim.
      * (* compress_coind *) destruct compress; try discriminate. apply tau_compress; auto. eapply H; eauto.
      * (* compress_ind *) destruct compress; discriminate.
    + (* tau_compress *) subst compress.
      eapply tau_compress; eauto.
    + (* tau_div *) subst compress.
      eapply tau_div; eauto with optsim. assert (simF SimOpt.compress_mut lock expand ub `x false s' t).  eapply divpres_nocompress_r. split. intros _. apply DIV. now intro. apply H1. now apply H2.
    + (* tau_expand *)
      rewrite itr_str_r in TR. destruct TR as [t'1 TR1 TR2].
      subst.
      eapply sim_inv_taustar_l in H1; eauto.
      apply (gfp_fp (simF _ _ _ _)) in H1.
      apply H1 in TR2; auto.
      destruct compress; destruct TR2; try discriminate; eauto with optsim.
  - destruct H0. apply (gfp_fp (simF _ _ _ _)) in H1 as (_ & _ & ?); auto. intuition.
Qed.

Theorem upto_sim_l :
  forall compress lock expand ub (R : Chain (simF compress lock expand ub)) s s' t
    (OBS : Transitive Robs),
  `R true s' t ->
  sim compress lock SimOpt.noexpand ub true s s' ->
  `R true s t.
Proof.
  intros ?????.
  apply tower. {
    intros ??????????. red.
    eapply H; eauto.
    apply leq_infx in H2. apply H2, H0.
  }
  intros.
  split; intros; try discriminate. clear H2.
  repeat split; intros; subst.
  - apply (gfp_fp (simF _ _ _ _)) in H1. destruct H1 as [_ ?]. specialize (H1 eq_refl).
    apply H1 in H2 as [].
    + apply H0 in TR; auto. destruct TR; eauto with optsim.
    + discriminate.
  - apply (gfp_fp (simF _ _ _ _)) in H1. destruct H1 as [_ ?]. specialize (H1 eq_refl).
    apply H1 in H2 as [].
    + (* tau_exact *)
      apply H0 in TR as ?; auto. destruct H2; eauto with optsim.
      (* compress_mut *) subst. apply tau_div; eauto.
      assert (simF SimOpt.compress_mut lock expand ub `x false s'0 t). eapply divpres_trans_l with (t := t'). split; intro; try discriminate. apply DIV. admit.
      apply H2; auto.
    + (* tau_compress *) subst compress.
      eapply tau_compress; eauto. eapply H; eauto. apply (b_chain x). apply H0.
    + (* tau_div *) subst compress.
      eapply tau_div; eauto with optsim.
      eapply H; eauto. apply (b_chain x). apply H0.
      apply simF_f_t in H0; auto. apply divpres_trans_l with (s := s'0) in H0. now apply H0. admit.
    + (* tau_expand *)
      discriminate.
  - destruct H0. apply (gfp_fp (simF _ _ _ _)) in H1 as (_ & _ & ?); auto. intuition.
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
