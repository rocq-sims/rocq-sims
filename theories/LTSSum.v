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

(* TODO clean up this mess *)

(* LTS sum *)

Definition rel_sum {A B} (R : relation A) (R' : relation B) x y :=
  match x, y with
  | inl a, inl a' => R a a'
  | inr b, inr b' => R' b b'
  | _, _ => False
  end.

Program Definition EqType_sum (X Y : EqType) :=
  {| type_of := X.(type_of) + Y.(type_of); Eq := rel_sum X.(Eq) Y.(Eq) |}.
Next Obligation.
  split.
  - cbn. red. now intros [].
  - cbn. intros [] [] ?; cbn in *; auto; now symmetry.
  - cbn. intros [] [] []; cbn; try easy; intros; etransitivity; eauto.
Qed.

Program Definition trans_sum (lts lts' : LTS) (l : label) :
  srel (EqType_sum lts.(St) lts'.(St)) (EqType_sum lts.(St) lts'.(St)) :=
{|
  hrel_of s t :=
    match l, s, t with
    | tau, inl s, inl s' => lts.(trans) tau s s'
    | tau, inr t, inr t' => lts'.(trans) tau t t'
    | obs o', inl s, inl s' => exists o, lts.(trans) (obs o) s s' /\ o' = inl o
    | obs o', inr t, inr t' => exists o, lts'.(trans) (obs o) t t' /\ o' = inr o
    | _, _, _ => False
    end
|}.
Next Obligation.
  repeat split; now intuition.
Qed.
Next Obligation.
  repeat split; now intuition.
Qed.
Next Obligation.
  repeat split; now intuition.
Qed.
Next Obligation.
  repeat split; now intuition.
Qed.
Next Obligation.
  repeat split; try now intuition.
  - destruct l, x, y, x0, y0; cbn in *; intros; eauto with exfalso.
    + destruct H1 as (? & ? & ->).
      exists x. split; auto. now rewrite <- H, <- H0.
    + destruct H1 as (? & ? & ->).
      exists x. split; auto. now rewrite <- H, <- H0.
    + now rewrite <- H, <- H0.
    + now rewrite <- H, <- H0.
  - destruct l, x, y, x0, y0; cbn in *; intros; eauto with exfalso.
    + destruct H1 as (? & ? & ->).
      exists x. split; auto. now rewrite H, H0.
    + destruct H1 as (? & ? & ->).
      exists x. split; auto. now rewrite H, H0.
    + now rewrite H, H0.
    + now rewrite H, H0.
Qed.

Definition Robs_sum {O O'} (Robs : O -> O' -> Prop) (o o' : O + O') :=
  match o, o' with
  | inl o, inr o' => Robs o o'
  | _, _ => False
  end.

Definition lts_sum (lts lts' : LTS) Robss := {|
  Observable := lts.(Observable) + lts'.(Observable);
  St := EqType_sum lts.(St) lts'.(St);
  trans := trans_sum lts lts';
  Robs := Robs_sum Robss;
|}.

(* LTS injection *)

Definition label_inj {O O'} (obs_inj : O -> O') :
    @label O -> @label O' :=
  fun l =>
    match l with
    | tau => tau
    | obs o => obs (obs_inj o)
    end.

Definition lts_inj {lts lts' : LTS}
    (obs_inj : lts.(Observable) -> lts'.(Observable))
    (st_inj : lts.(St) -> lts'.(St))
    (st_inj_eq : Proper (lts.(St).(Eq) ==> lts'.(St).(Eq)) st_inj) : Prop :=
  (forall l s s', lts.(trans) l s s' -> lts'.(trans) (label_inj obs_inj l) (st_inj s) (st_inj s')) /\
  (forall l' s t', lts'.(trans) l' (st_inj s) t' -> exists l s', l' = label_inj obs_inj l /\ t' = st_inj s' /\ lts.(trans) l s s').

(* Lemmas about LTS injection *)

Lemma lts_inj_taustar {lts lts' : LTS} :
  forall obs_inj st_inj st_inj_eq s t,
  lts_inj obs_inj st_inj st_inj_eq ->
  (lts.(trans) tau)^* s t ->
  (lts'.(trans) tau)^* (st_inj s) (st_inj t).
Proof.
  intros.
  apply srel_str_ind_l' with (i := trans tau) (P := fun s t => (trans tau)^* (st_inj s) (st_inj t)); auto.
  - cbn -[str]. intros. now rewrite <- H1, <- H2.
  - intros. rewrite H1. now exists O.
  - intros. rewrite str_unfold_l. right.
    esplit; eauto. now apply H in H1.
Qed.

Lemma lts_inj_taustar' {lts lts' : LTS} :
  forall obs_inj st_inj st_inj_eq s t',
  lts_inj obs_inj st_inj st_inj_eq ->
  (lts'.(trans) tau)^* (st_inj s) t' ->
  exists s', lts'.(St).(Eq) t' (st_inj s') /\ (lts.(trans) tau)^* s s'.
Proof.
  intros. remember (st_inj s) as t.
  assert (lts'.(St).(Eq) t (st_inj s)) by now subst.
  clear Heqt. revert s H1.
  apply srel_str_ind_r' with (i := trans tau)
    (P := fun t t' => forall s : St lts,
      Eq (St lts') t (st_inj s) -> exists s' : St lts, Eq (St lts') t' (st_inj s') /\ (trans tau)^* s s'); auto.
  - cbn -[str]. intros. rewrite <- H1 in H4. apply H3 in H4 as (? & ? & ?).
    subst. exists x1. split; auto. now rewrite <- H2.
  - intros. exists s0. split. now rewrite <- H1. now exists O.
  - intros. apply H1 in H3 as (? & ? & ?).
    rewrite H3 in H2. apply H in H2 as (? & ? & ? & ? & ?). subst.
    destruct x0; try discriminate. clear H2.
    exists x1. split; auto. rewrite str_unfold_r. right.
    esplit; eauto.
Qed.

Lemma lts_inj_dtrans {lts lts' : LTS} :
  forall obs_inj st_inj st_inj_eq delay l s t,
  lts_inj obs_inj st_inj st_inj_eq ->
  dtrans (lts := lts) delay l s t ->
  dtrans (lts := lts') delay (label_inj obs_inj l) (st_inj s) (st_inj t).
Proof.
  intros. destruct delay.
  2: now apply H in H0.
  destruct H0. eapply lts_inj_taustar in H0; eauto.
  apply H in H1. esplit; eauto.
Qed.

Lemma lts_inj_dtrans' {lts lts' : LTS} :
  forall obs_inj st_inj st_inj_eq delay l' s t',
  lts_inj obs_inj st_inj st_inj_eq ->
  dtrans (lts := lts') delay l' (st_inj s) t' ->
  exists l s', l' = label_inj obs_inj l /\ lts'.(St).(Eq) t' (st_inj s') /\ dtrans (lts := lts) delay l s s'.
Proof.
  intros. destruct delay.
  2: { apply H in H0 as (? & ? & ? & ? & ?). subst. eauto. }
  destruct H0.
  eapply lts_inj_taustar' in H0 as (? & ? & ?); eauto.
  rewrite H0 in H1. apply H in H1 as (? & ? & ? & ? & ?). subst.
  exists x1, x2. repeat split; auto.
  esplit; eauto.
Qed.

Lemma lts_inj_tauplus {lts lts' : LTS} :
  forall obs_inj st_inj st_inj_eq s t,
  lts_inj obs_inj st_inj st_inj_eq ->
  (lts.(trans) tau)^+ s t ->
  (lts'.(trans) tau)^+ (st_inj s) (st_inj t).
Proof.
  intros.
  eapply dtrans_tauplus. change tau with (label_inj obs_inj tau). eapply lts_inj_dtrans; eauto.
  now apply tauplus_dtrans.
Qed.

Lemma lts_inj_tauplus' {lts lts' : LTS} :
  forall obs_inj st_inj st_inj_eq s t',
  lts_inj obs_inj st_inj st_inj_eq ->
  (lts'.(trans) tau)^+ (st_inj s) t' ->
  exists s', lts'.(St).(Eq) t' (st_inj s') /\ (lts.(trans) tau)^+ s s'.
Proof.
  intros.
  apply tauplus_dtrans in H0. change tau with (label_inj obs_inj tau) in H0. eapply lts_inj_dtrans' in H0; eauto.
  destruct H0 as (? & ? & ? & ? & ?).
  destruct x; try discriminate.
  apply dtrans_tauplus in H2. eauto.
Qed.

Lemma lts_inj_is_stuck {lts lts' : LTS} :
  forall obs_inj st_inj st_inj_eq s,
  lts_inj obs_inj st_inj st_inj_eq ->
  is_stuck (lts := lts) s ->
  is_stuck (lts := lts') (st_inj s).
Proof.
  intros. intros [].
  apply H in H1 as (? & ? & ? & ? & ?). subst. esim.
Qed.

Lemma lts_inj_is_stuck' {lts lts' : LTS} :
  forall obs_inj st_inj st_inj_eq s,
  lts_inj obs_inj st_inj st_inj_eq ->
  is_stuck (lts := lts') (st_inj s) ->
  is_stuck (lts := lts) s.
Proof.
  intros. intros [].
  apply H in H1. esim.
Qed.

Lemma lts_inj_can_be_stuck {lts lts' : LTS} :
  forall obs_inj st_inj st_inj_eq delay s,
  lts_inj obs_inj st_inj st_inj_eq ->
  can_be_stuck (lts := lts) delay s ->
  can_be_stuck (lts := lts') delay (st_inj s).
Proof.
  intros. destruct H0 as [| (? & ? & ? & ?)].
  - eapply lts_inj_is_stuck in H0; eauto. now left.
  - eapply lts_inj_taustar in H1; eauto.
    eapply lts_inj_is_stuck in H2; eauto.
    right. esim.
Qed.

Lemma lts_inj_can_be_stuck' {lts lts' : LTS} :
  forall obs_inj st_inj st_inj_eq delay s,
  lts_inj obs_inj st_inj st_inj_eq ->
  can_be_stuck (lts := lts') delay (st_inj s) ->
  can_be_stuck (lts := lts) delay s.
Proof.
  intros. destruct H0 as [| (? & ? & ? & ?)].
  - eapply lts_inj_is_stuck' in H0; eauto. now left.
  - eapply lts_inj_taustar' in H1 as (? & ? & ?); eauto.
    rewrite H1 in H2. eapply lts_inj_is_stuck' in H2; eauto.
    right. esim.
Qed.

(* Injection into LTS sum *)

Program Definition lts_sum_inj_l {lts lts'} Robss :=
  lts_inj (lts := lts) (lts' := lts_sum lts lts' Robss) inl inl _.

Lemma lts_sum_inj_l_correct {lts lts'} Robss :
  @lts_sum_inj_l lts lts' Robss.
Proof.
  split; intros.
  - destruct l; auto.
    cbn. eauto.
  - destruct l'; cbn in *.
    + destruct t'; try easy.
      destruct H as (? & ? & ->).
      exists (obs x). eauto.
    + exists tau. destruct t'; now eauto.
Qed.

Program Definition lts_sum_inj_r {lts lts'} Robss :=
  lts_inj (lts := lts') (lts' := lts_sum lts lts' Robss) inr inr _.

Lemma lts_sum_inj_r_correct {lts lts'} Robss :
  @lts_sum_inj_r lts lts' Robss.
Proof.
  split; intros.
  - destruct l; auto.
    cbn. eauto.
  - destruct l'; cbn in *.
    + destruct t'; try easy.
      destruct H as (? & ? & ->).
      exists (obs x). eauto.
    + exists tau. destruct t'; now eauto.
Qed.

(* Transporting similarity results *)

Theorem sim_inj {lts lts' : LTS} (Hobs : Transitive lts.(Robs)) :
  forall freeze lock delay obs_inj st_inj st_inj_eq b s t
  (INJ : lts_inj obs_inj st_inj st_inj_eq)
  (INJ' : forall o o', lts.(Robs) o o' -> lts'.(Robs) (obs_inj o) (obs_inj o')),
  sim (lts := lts) freeze lock delay b s t ->
  sim (lts := lts') freeze lock delay b (st_inj s) (st_inj t).
Proof.
  intros ???. red. coinduction R CH. intros.
  destruct b. 2: {
    apply sim_fp in H. induction H.
    apply simF_equiv. constructor. intros ??.
    apply INJ in H0 as (? & ? & ? & ? & ?). subst.
    destruct x; try discriminate. clear H0.
    apply H in H2 as [].
    - apply INJ in TR. esim.
    - apply dtau_div.
      destruct DIV as [_ ?]. apply simF_equiv in H0. apply H0.
  }
  apply simF_equiv. apply sim_fp in H.
  repeat split; intros.
  - apply INJ in H0 as (? & ? & ? & -> & ?).
    destruct x; try discriminate. inversion_clear H0.
    apply H in H1 as [].
    eapply lts_inj_dtrans in TR; eauto.
    econstructor; eauto.
    apply itr_sim in SIM; auto. apply itr_ext_hrel. eapply CH; eauto.
  - apply INJ in H0 as (? & ? & ? & -> & ?).
    destruct x; try discriminate. clear H0.
    apply H in H1 as []; esim.
    + apply INJ in TR. esim.
    + eapply lts_inj_tauplus in TR; esim.
  - red. destruct H as (_ & _ & []); auto.
    right. intro. eapply lts_inj_is_stuck' in H0; eauto.
    apply H in H0. eapply lts_inj_can_be_stuck; eauto.
Qed.

Theorem sim_inj' {lts lts' : LTS} (Hobs : Transitive lts'.(Robs)) :
  forall freeze lock delay obs_inj st_inj st_inj_eq b s t
  (INJ : lts_inj obs_inj st_inj st_inj_eq)
  (INJ' : forall o o', lts'.(Robs) (obs_inj o) (obs_inj o') -> lts.(Robs) o o'),
  sim (lts := lts') freeze lock delay b (st_inj s) (st_inj t) ->
  sim (lts := lts) freeze lock delay b s t.
Proof.
  intros ???. red. coinduction R CH. intros.
  destruct b. 2: {
    apply sim_fp in H.
    remember (st_inj s) as s'. remember (st_inj t) as t'.
    revert s t Heqs' Heqt'. induction H. intros. subst.
    apply simF_equiv. constructor. intros ??.
    apply INJ in H0.
    apply H in H0 as [].
    - apply INJ in TR as (? & ? & ? & ? & ?). subst.
      destruct x; try discriminate. esim.
    - apply dtau_div.
      destruct DIV as [_ ?].
      specialize (H0 s' t0 eq_refl eq_refl).
      eapply simF_equiv in H0. apply H0.
  }
  apply simF_equiv. apply sim_fp in H.
  repeat split; intros.
  - apply INJ in H0.
    apply H in H0 as [].
    eapply lts_inj_dtrans' in TR as (? & ? & ? & ? & ?); eauto.
    destruct x; try discriminate. inversion H0. subst. clear H0.
    rewrite H1 in SIM.
    econstructor; eauto.
    apply itr_sim in SIM; auto. apply itr_ext_hrel. eapply CH; eauto.
  - apply INJ in H0.
    apply H in H0 as []; esim.
    + apply INJ in TR as (? & ? & ? & ? & ?). subst.
      destruct x; try discriminate. esim.
    + eapply lts_inj_tauplus' in TR as (? & ? & ?); eauto.
      rewrite H1 in SIM. esim.
  - red. destruct H as (_ & _ & []); auto.
    right. intro. eapply lts_inj_is_stuck in H0; eauto.
    apply H in H0. eapply lts_inj_can_be_stuck'; eauto.
Qed.

Definition Robs_trans {lts lts' lts'' : LTS}
    (Robs12 : lts.(Observable) -> lts'.(Observable) -> Prop)
    (Robs23 : lts'.(Observable) -> lts''.(Observable) -> Prop)
    (o o' : (lts.(Observable) + lts''.(Observable))) :=
  match o, o' with
  | inl o, inr o' => exists o'', Robs12 o o'' /\ Robs23 o'' o'
  | _, _ => False
  end.

Definition Robs_trans' {lts lts' lts'' : LTS}
    (Robs12 : lts.(Observable) -> lts'.(Observable) -> Prop)
    (Robs23 : lts'.(Observable) -> lts''.(Observable) -> Prop)
    (o : (lts.(Observable) + lts'.(Observable))) o' :=
  match o, o' with
  | inl o, o' => exists o'', Robs12 o o'' /\ Robs23 o'' o'
  | _, _ => False
  end.

Definition Robs_trans'' {lts lts' lts'' : LTS}
    (Robs12 : lts.(Observable) -> lts'.(Observable) -> Prop)
    (Robs23 : lts'.(Observable) -> lts''.(Observable) -> Prop)
    (o : lts.(Observable)) (o' : lts''.(Observable)) :=
   exists o'', Robs12 o o'' /\ Robs23 o'' o'.

Definition Robs_sum3 {lts lts' lts'' : LTS}
    (Robs12 : lts.(Observable) -> lts'.(Observable) -> Prop)
    (Robs23 : lts'.(Observable) -> lts''.(Observable) -> Prop)
    (o o' : (lts.(Observable) + lts'.(Observable)) + lts''.(Observable)) :=
  match o, o' with
  | inl (inl o), inl (inr o') => Robs12 o o'
  | inl (inr o), inr o' => Robs23 o o'
  | inl (inl o), inr o' => exists o'', Robs12 o o'' /\ Robs23 o'' o'
  | _, _ => False
  end.

Definition lts_sum3 (lts lts' lts'' : LTS) Robs12 Robs23 := {|
  Observable := lts.(Observable) + lts'.(Observable) + lts''.(Observable);
  St := EqType_sum (EqType_sum lts.(St) lts'.(St)) lts''.(St);
  trans := trans_sum (lts_sum lts lts' Robs12) lts'';
  Robs := Robs_sum3 Robs12 Robs23;
|}.

(*Definition lts_sum3 lts lts' lts'' Robs12 Robs23 :=
  lts_sum (lts_sum lts lts' Robs12) lts'' (Robs_trans' Robs12 Robs23).*)

Program Definition lts_sum_inj_12 {lts lts' lts''} Robs12 Robs23 :=
  lts_inj (lts := lts_sum lts lts' Robs12) (lts' := lts_sum3 lts lts' lts'' Robs12 Robs23) inl inl _.

Lemma lts_sum_inj_12_correct {lts lts' lts''} Robs12 Robs23 :
  @lts_sum_inj_12 lts lts' lts'' Robs12 Robs23.
Proof.
  split; intros.
  - destruct l as [[]|], s, s'; cbn in *; auto with exfalso.
    + destruct H as (? & ? & ?). inversion H0. eauto.
    + destruct H as (? & ? & ?). inversion H0.
    + destruct H as (? & ? & ?). inversion H0.
    + destruct H as (? & ? & ?). inversion H0. eauto.
  - destruct l' as [[[] |] |]; cbn in *.
    + destruct s, t' as [[]|]; cbn in *; try easy.
      all: destruct H as (? & ? & ?); inversion H0; try easy.
      * subst. destruct H as (? & ? & ?). inversion H1.
        subst. exists (obs (inl x)). exists (inl t0). eauto.
      * destruct H as (? & ? & ?). subst. inversion H2.
    + exists (obs (inr o)). destruct s, t' as [[]|]; cbn in H; try easy.
      all: destruct H as (? & ? & ?); inversion H0; try easy.
      destruct H as (? & ? & ?). subst. inversion H2. subst.
      exists (inr t0). eauto.
    + destruct s, t' as [[]|]; cbn in H; try easy.
      all: destruct H as (? & ? & ?); inversion H0; try easy.
    + exists tau. destruct s, t' as [[] |]; cbn in H; try now eauto.
Qed.

Definition inj23 {A B C} (bc : B + C) : A + B + C :=
  match bc with
  | inl b => inl (inr b)
  | inr c => inr c
  end.

Program Definition lts_sum_inj_23 {lts lts' lts''} Robs12 Robs23 :=
  lts_inj (lts := lts_sum lts' lts'' Robs23) (lts' := lts_sum3 lts lts' lts'' Robs12 Robs23) inj23 inj23 _.
Next Obligation.
  destruct x, y; auto.
Qed.

Lemma lts_sum_inj_23_correct {lts lts' lts''} Robs12 Robs23 :
  @lts_sum_inj_23 lts lts' lts'' Robs12 Robs23.
Proof.
  split; intros.
  - destruct l as [[]|], s, s'; auto; cbn in *.
    + destruct H as (? & ? & ?). inversion H0. eauto.
    + destruct H as (? & ? & ?). inversion H0.
    + destruct H as (? & ? & ?). inversion H0.
    + destruct H as (? & ? & ?). inversion H0. eauto.
  - destruct l' as [[[] |] |]; cbn in *.
    + destruct s, t' as [[]|]; cbn in *; try easy.
      all: destruct H as (? & ? & ?); inversion H0; try easy.
      subst. destruct H as (? & ? & ?). inversion H1.
    + exists (obs (inl o)). destruct s, t' as [[]|]; cbn in H; try easy.
      all: destruct H as (? & ? & ?); inversion H0; try easy.
      destruct H as (? & ? & ?). subst. inversion H2. subst.
      exists (inl t0). eauto.
    + exists (obs (inr o)). destruct s, t' as [[]|]; cbn in H; try now eauto.
      all: destruct H as (? & ? & ?); inversion H0; try easy.
      exists (inr t0). eauto.
    + exists tau. destruct s, t' as [[] |]; cbn in H; try now eauto.
      * exists (inl t0). auto.
      * exists (inr t0). auto.
Qed.

Definition inj13 {A B C} (ac : A + C) : A + B + C :=
  match ac with
  | inl a => inl (inl a)
  | inr c => inr c
  end.

Program Definition lts_sum_inj_13 {lts lts' lts''} Robs12 Robs23 :=
  lts_inj (lts := lts_sum lts lts'' (Robs_trans'' Robs12 Robs23)) (lts' := lts_sum3 lts lts' lts'' Robs12 Robs23) inj13 inj13 _.
Next Obligation.
  destruct x, y; auto.
Qed.

Lemma lts_sum_inj_13_correct {lts lts' lts''} Robs12 Robs23 :
  @lts_sum_inj_13 lts lts' lts'' Robs12 Robs23.
Proof.
  split; intros.
  - destruct l as [[]|], s, s'; auto; cbn in *.
    + destruct H as (? & ? & ?). inversion H0. eauto.
    + destruct H as (? & ? & ?). inversion H0.
    + destruct H as (? & ? & ?). inversion H0.
    + destruct H as (? & ? & ?). inversion H0. eauto.
  - destruct l' as [[[] |] |]; cbn in *.
    + exists (obs (inl o)). destruct s, t' as [[]|]; cbn in H; try now eauto.
      all: destruct H as (? & ? & ?); inversion H0; try easy.
      destruct H as (? & ? & ?). subst. inversion H2. subst.
      exists (inl t0). eauto.
    + destruct s, t' as [[]|]; cbn in H; try easy.
      all: destruct H as (? & ? & ?); inversion H0; try easy.
      subst.
      destruct H as (? & ? & ?). inversion H1.
    + exists (obs (inr o)). destruct s, t' as [[]|]; cbn in H; try now eauto.
      all: destruct H as (? & ? & ?); inversion H0; try easy. subst.
      exists (inr t0). eauto.
    + exists tau. destruct s, t' as [[] |]; cbn in H; try now eauto.
      * exists (inl t0). auto.
      * exists (inr t0). auto.
Qed.

Theorem sim_trans_h {lts lts' lts'' : LTS} Robs12 Robs23 freeze lock delay :
  forall s t u,
  sim (lts := lts_sum lts lts' Robs12) freeze lock delay true (inl s) (inr t) ->
  sim (lts := lts_sum lts' lts'' Robs23) freeze lock delay true (inl t) (inr u) ->
  sim (lts := lts_sum lts lts'' (Robs_trans'' Robs12 Robs23)) freeze lock delay true (inl s) (inr u).
Proof.
  intros.
  set (lts''' := lts_sum3 lts lts' lts'' Robs12 Robs23).
  eapply (sim_inj' (lts' := lts''')) with (st_inj := inj13).
  { cbn. intros [[]|] [[]|] [[]|]; cbn; intros; eauto with exfalso. }
  apply lts_sum_inj_13_correct.
  { intros. now destruct o, o'. }
  cbn. eapply sim_trans with (y := (inl (inr t))).
  { cbn. intros [[]|] [[]|] [[]|]; cbn; intros; eauto with exfalso. }
  - eapply (sim_inj (lts := lts_sum lts lts' Robs12)).
    { cbn. intros [] [] []; cbn; auto with exfalso. }
    eapply lts_sum_inj_12_correct.
    { intros. destruct o, o'; cbn in *; auto. }
    apply H.
  - change (inl (inr t)) with (inj23 (A := St lts) (C := St lts'') (inl t)).
    change (inr u) with (inj23 (A := St lts) (B := St lts') (inr u)).
    eapply (sim_inj (lts := lts_sum lts' lts'' Robs23)) with (st_inj := inj23).
    { cbn. intros [] [] []; cbn; auto with exfalso. }
    apply lts_sum_inj_23_correct.
    { intros. destruct o, o'; auto. }
    apply H0.
  Unshelve.
  { cbn. intros. destruct x, y; auto. }
  { cbn. intros. destruct x, y; auto. }
  { cbn. intros. destruct x, y; auto. }
Qed.
