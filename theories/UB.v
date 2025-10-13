(* SPDX-FileCopyrightText: 2025 rocq-sims authors *)
(* SPDX-License-Identifier: LGPL-3.0-or-later *)

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
From Sims Require Import Utils LTS Divergence Sims.

Import CoindNotations.


Section WithLTS.

Definition RUB {X} (R : relation X) o o' :=
  match o, o' with
  | Some o, Some o' => R o o'
  | _, None => True
  | _, _ => False
  end.

#[export] Instance RUB_Reflexive X (R : relation X) : Reflexive R -> Reflexive (RUB R).
Proof.
  intros ? []. cbn. apply H. reflexivity.
Qed.

(* Transition relation in which states in the 'ubs' set are given UB semantics *)
Variant utrans_ {lts} ubs : @label (option lts.(Observable)) -> St lts -> St lts -> Prop :=
(* Observable transitions are preserved *)
| utrans_obs_ l s t : trans (obs l) s t -> utrans_ ubs (obs (Some l)) s t
(* Tau transitions are preserved *)
| utrans_tau_ s t : trans tau s t -> utrans_ ubs tau s t
(* UB states can take *any* transition to *any* state,
   including transitions labelled with 'None' that only appear in UB states. *)
| utrans_ub_ l s t : ubs s -> utrans_ ubs l s t.
Hint Constructors utrans_ : optsim.

Obligation Tactic := idtac.
Program Definition utrans {lts} ubs (Hubs : Proper (lts.(St).(Eq) ==> iff) ubs) l : srel lts.(St) lts.(St) :=
  {| hrel_of := utrans_ ubs l |}.
Next Obligation.
  destruct l as [[] |]; split; intro; inversion H1; subst; rewrite ?H, ?H0 in *;
  try now constructor.
  - apply utrans_obs_. now rewrite H, H0.
  - inversion H1; subst.
    + apply utrans_obs_. now rewrite H, H0.
    + apply utrans_ub_. now rewrite H.
  - apply utrans_ub_. now rewrite H.
  - apply utrans_tau_. now rewrite H, H0.
  - apply utrans_ub_. now rewrite H.
Qed.

Hint Unfold hrel_of : optsim.
Hint Unfold trans : optsim.
Hint Unfold utrans : optsim.

Definition ubify lts ubs Hubs : LTS := {|
  Observable := option lts.(Observable); (* None = UB *)
  St := lts.(St);
  trans := utrans ubs Hubs;
  Robs := RUB lts.(Robs);
|}.

Lemma ub_lockpres : forall {lts} lock st' st
  ubs (Hubs : Proper (lts.(St).(Eq) ==> iff) ubs),
  ubs st' ->
  lockpres (lts := ubify lts ubs Hubs) lock SimOpt.delay st st'.
Proof.
  intros. destruct lock. 2: now left.
  right. intro. right. split; auto.
  exists st. split; auto. rewrite <- str_ext. now apply utrans_ub_.
Qed.

Lemma simF_ub_r : forall {lts} freeze lock delay (Hlock : lock = SimOpt.nolock \/ delay = SimOpt.delay)
  ubs (Hubs : Proper (lts.(St).(Eq) ==> iff) ubs)
  (R : Chain (simF freeze lock delay)) (REFL: Reflexive lts.(Robs)) st st',
  ubs st' ->
  simF (lts := ubify lts ubs Hubs) freeze lock delay `R true st st'.
Proof.
  intros. apply simF_equiv. repeat split; intros.
  - eapply ans_obs with (o' := o) (t' := s').
    + apply trans_dtrans. now apply utrans_ub_.
    + apply itr_ext_hrel. reflexivity.
    + reflexivity.
  - eapply tau_exact with (t' := s'). now apply utrans_ub_. reflexivity.
  - destruct Hlock; subst. now left. now apply ub_lockpres.
Qed.

Lemma ub_taustar : forall {lts} (st st' : lts.(St))
  ubs (Hubs : Proper (lts.(St).(Eq) ==> iff) ubs),
  (trans (lts := lts) tau)^* st st' ->
  (trans (lts := ubify lts ubs Hubs) tau)^* st st'.
Proof.
  intros. revert H. intro. apply srel_str_ind_l' with (i := trans (lts := lts) tau) (P := fun st st' =>
    (trans (lts := ubify lts ubs Hubs) tau)^* st st'); auto.
  - cbn -[str]. intros. now rewrite <- H0, <- H1.
  - intros. rewrite H0. now rewrite <- str_refl.
  - intros. rewrite str_unfold_l. right. esplit. apply utrans_tau_. apply H0. apply H1.
Qed.

End WithLTS.

Hint Constructors utrans_ : optsim.
