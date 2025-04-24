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
From OptSim Require Import Utils LTS OptSim.

Section WithLTS.

Context {lts : LTS}.
Context (freeze : SimOpt.freeze_opt) (lock : SimOpt.lock_opt) (delay : SimOpt.delay_opt).
Let Observable := lts.(Observable).
Let St := lts.(St).
Let trans := lts.(trans).
Let epsilon := lts.(epsilon).
Let Robs := lts.(Robs).
Let ub_state := lts.(ub_state).
Let label := @label Observable.

  (* TODO try to just use TauAnswer with Rind as Rdiv *)
  Variant TauIndAnswer (R Rind : relation St) s' t : Prop :=
  | taui_exact t' (TR : trans tau t t') (SIM : R s' t')
  | taui_freeze (_ : freeze = SimOpt.freeze) (SIM : R s' t)
  | taui_div (_ : freeze = SimOpt.freeze_div) (SIM : Rind s' t)
  | taui_delay t' (_ : delay = SimOpt.delay) (TR : (trans tau)^+ t t') (SIM : R s' t')
  .
  Hint Constructors TauIndAnswer : optsim.

  Definition simIndF R Rind s t :=
    (forall o s', trans (obs o) s s' ->
      ObsAnswer delay R s' t o
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

Lemma simInd_mon : forall R R', R <= R' -> simInd R <= simInd R'.
Proof.
  cbn. intros. induction H0.
  repeat split; intros.
  - apply H0 in H1 as []; esim.
  - apply H0 in H1 as []; esim.
    destruct SIM. esim.
  - apply H0.
Qed.

End WithLTS.
