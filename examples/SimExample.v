(* SPDX-FileCopyrightText: 2025 rocq-sims authors *)
(* SPDX-License-Identifier: LGPL-3.0-or-later *)

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
From Sims Require Import Utils LTS Divergence Sims.

Import CoindNotations.

Variant St :=
| t0 | t1 | t2 | t3 | t4 | u0 | u1 | u2 | u3.

Variant Obs :=
| a | b.

Variant trans : @label Obs -> St -> St -> Prop :=
| t0t0 : trans tau t0 t0
| t0t1 : trans tau t0 t1
| t0t3 : trans (obs b) t0 t3
| t1t2 : trans (obs a) t1 t2
| t3t4 : trans tau t3 t4
| u0u1 : trans tau u0 u1
| u0u3 : trans (obs b) u0 u3
| u1u1 : trans tau u1 u1
| u1u2 : trans (obs a) u1 u2
.

Program Definition lts := {|
  Observable := Obs;
  LTS.St := {| type_of := St |};
  LTS.trans := fun l => {| hrel_of := trans l |};
  Robs := eq
|}.

Lemma divpres_t0_u0 :
  divpres (lts := lts) t0 u0.
Proof.
  red. apply Divergence.diverges_divpres.
  red. coinduction R CH. cbn.
  exists u1. split. { apply u0u1. }
  accumulate CH'.
  exists u1. split. { apply u1u1. }
  apply CH'.
Qed.

Theorem sim_t0_u0 :
  sim (lts := lts) SimOpt.freeze_div SimOpt.nolock SimOpt.delay true t0 u0.
Proof.
  red.
  (* We start with {(t0, u0)} as our simulation candidate *)
  coinduction R CH.
  apply simF_equiv.
  (* We unfold the simulation game *)
  repeat split. 3: now left.
  - intros. inversion H. subst. clear H.
    (* Case 1: t0t3, answered with u0u3 *)
    apply ans_obs with (o' := b) (t' := u3); auto.
    { apply trans_dtrans. apply u0u3. }
    apply itr_ext_hrel.
    (* We apply the simulation up-to simulation step technique
       (included in the coinduction library),
       and the left up-to tau technique. *)
    apply (b_chain R).
    apply upto_tau_l; auto.
    { red. intros. now inversion H. }
    intros. do 2 red. inversion H. clear H. subst.
    (* There is no outgoing transition from t4, which makes the simulation game trivial. *)
    apply simF_equiv. repeat split. 3: now left.
    all: intros; now inversion H.
  - intros. inversion H; subst; clear H.
    + (* Case 2: t0t0, answered by u0 stagnating *)
      apply tau_div; auto.
      (* `R false is Rdiv in the paper, we can get rid of it with Lemma 3.3 *)
      apply simF_f_divpres.
      apply divpres_t0_u0.
    + (* Case 3: t0t1, answered with u0u1 *)
      apply tau_exact with (t' := u1). { apply u0u1. }
      (* We apply the up-to simulation step technique and unfold the simulation game. *)
      apply (b_chain R).
      apply simF_equiv. repeat split; intros. 3: now left.
      2: { now inversion H. }
      inversion H. subst. clear H.
      (* To t1t2, u1 answers with u1u2 *)
      apply ans_obs with (o' := a) (t' := u2); auto.
      { apply trans_dtrans, u1u2. }
      apply itr_ext_hrel.
      (* t2 is stuck, so we apply the up-to step technique
         to play a trivial simulation game one last time *)
      apply (b_chain R). apply simF_equiv. repeat split; intros.
      3: now left. all: now inversion H.
Qed.
