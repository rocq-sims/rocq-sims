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

Definition RL l l' :=
  match l, l' with
  | tau, tau => True
  | obs o, obs o' => Robs o o'
  | _, _ => False
  end.

Variant TraceAnswer l (t t' : St) : Prop :=
| ans_exact l' t' (TR : trans l' t t') (LBL : RL l l')
| ans_freeze (_ : freeze = SimOpt.freeze_div) (LBL : l = tau)
| ans_delay l' t' (_ : delay = SimOpt.delay) (TR : ((trans tau)^+ ⋅ trans l') t t') (LBL : RL l l')
.

(* we could do without the "exists t'", with something like R true s' (fun t' => trans l t t') *)
Definition simGame (R : bool -> St -> (St -> Prop) -> Prop) s T :=
  (forall l s', trans l s s' ->
    exists T' : St -> Prop, R true s' T' /\ R false s' T' /\ forall t', T' t' ->
      exists t, T t /\ TraceAnswer l t t').

Variant simF_ R : bool -> hrel St (St -> Prop) :=
| simF_game s T : simGame R s T -> simF_ R true s T
| simF_divpres s T : (exists t, T t /\ divpresF (fun s t => R false s (fun t' => St.(Eq) t t')) s t) -> simF_ R false s T.

Program Definition simF :
  mon (bool -> hrel St (St -> Prop)) :=
{| body R b s T :=
  simF_ R b s T
|}.
Next Obligation.
  destruct H0; constructor; repeat split; intros.
  intros ???. apply H0 in H1 as (? & ? & ? & ?). exists x0. split; auto.
  destruct H0 as (? & ? & ?). exists x0. split; auto.
  induction H1. constructor. intros ??.
  apply H1 in H2 as [].
  - eapply dtau_match; eauto.
  - apply dtau_div. now apply DIV.
Qed.

Definition sim := gfp simF.

CoInductive trace :=
| Cons (l : Observable) (s : trace)
| Div
| Nil.

Program Definition htr :
  mon (trace -> St -> Prop) :=
  {| body R tr s :=
    match tr with
    | Cons l tr' => exists s', ((trans tau)^*⋅trans (obs l)) s s' /\ R tr' s'
    | Nil => True
    | Div => diverges s
    end
  |}.
Next Obligation.
  destruct a. destruct H0 as (? & ? & ?). eauto. apply H0. apply H0.
Defined.

Definition has_trace := gfp htr.

Definition tracincl (s : St) (s' : St) :=
  forall tr, has_trace tr s -> has_trace tr s'.

Theorem sim_tracincl : forall s T,
  (forall tr, has_trace tr s -> exists t, T t /\ has_trace tr t) -> sim true s T.
Proof.
  red. coinduction R CH. intros.
  constructor. red. intros.
  destruct l.
  - exists (fun t' => exists t, T t /\ ((trans tau)^*⋅trans (obs s0)) t t'). repeat split.
    + apply CH. intros.
      specialize (H (Cons s0 tr)).
      lapply H.
      * intro. destruct H2 as (? & ? & ?).
        apply (gfp_fp htr) in H3. cbn -[str dot] in H3.
        destruct H3 as (? & ? & ?).
        exists x0. split; auto. exists x. split; auto.
      * apply (gfp_fp htr). cbn -[str dot]. exists s'. split; auto. admit.
    + destruct (diverges_lem s').
      * apply (gfp_chain R). apply (gfp_fp simF).
        specialize (H (Cons s0 Div)).
        lapply H. 2: admit.
        intros (? & ? & ?). constructor.
        apply (gfp_fp htr) in H3. cbn -[str dot] in H3.
        destruct H3 as (? & ? & ?).
        exists x0. split. exists x. auto.
        admit.
      * admit.
    + intros. destruct H1 as (? & ? & ?).
      exists x. split; auto.
      eapply ans_delay. admit. admit. admit.
  - exists T. repeat split.
    + apply CH. intros.
      assert (has_trace tr s) by admit. apply H in H2. apply H2.
    + destruct (diverges_lem s').
      * apply (gfp_chain R). apply (gfp_fp simF).
        specialize (H Div).
        lapply H. 2: admit.
        intros (? & ? & ?). constructor.
        apply (gfp_fp htr) in H3. cbn -[str dot] in H3.
        exists x. split; auto. admit.
      * admit.
    + intros.
        exists t'. split; auto.
        eapply ans_freeze. admit. admit.
Admitted.

End SimDef.
End WithLTS.
