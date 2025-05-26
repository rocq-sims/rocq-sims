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

Hint Unfold car_of : core.

Create HintDb optsim.
#[global] Ltac esim := eauto 10 with optsim exfalso.

(* RA lemmas *)

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
  Proper (E.(Eq) ==> impl) P ->
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
  apply proper_sym_impl_iff in H. 2: typeclasses eauto.
  cbn. intros. now rewrite H3, H4.
Qed.

Lemma srel_str_ind_r {E : EqType} :
  forall (P : E -> Prop) (i : srel E E),
  Proper (E.(Eq) ==> impl) P ->
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
  apply proper_sym_impl_iff in H. 2: typeclasses eauto.
  cbn. intros. now rewrite H3, H4.
Qed.

Lemma srel_str_ind_l' {E : EqType} :
  forall (i : srel E E) (P : E -> E -> Prop),
  Proper (E.(Eq) ==> E.(Eq) ==> impl) P ->
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
  Unshelve. apply proper_sym_impl_iff_2; typeclasses eauto.
Qed.

Lemma srel_itr_ind_l' {E : EqType} :
  forall (i : srel E E) (P : E -> E -> Prop),
  Proper (E.(Eq) ==> E.(Eq) ==> impl) P ->
  (forall s t, i s t -> P s t) ->
  (forall s t u, i s t -> P t u -> P s u) ->
  forall s t, i^+ s t -> P s t.
Proof.
  intros.
  eset (P' := {| hrel_of := fun s t => P s t|} : srel E E).
  epose proof (itr_ind_l1 (X := srel_monoid_ops)). specialize (H3 E i P'). cbn in H3. eapply H3.
  - intros. now apply H0.
  - intros. red in H4. destruct H4. eapply H1; eauto.
  - apply H2.
  Unshelve. apply proper_sym_impl_iff_2; typeclasses eauto.
Qed.

Lemma hrel_itr_ind_l' {X : Type} :
  forall (i : hrel X X) (P : X -> X -> Prop),
  (forall s t, i s t -> P s t) ->
  (forall s t u, i s t -> P t u -> P s u) ->
  forall s t, i^+ s t -> P s t.
Proof.
  intros.
  epose proof (itr_ind_l1 (X := hrel_monoid_ops)). specialize (H2 X i P). cbn in H2. eapply H2.
  - intros. now apply H.
  - intros. red in H3. destruct H3. eapply H0; eauto.
  - apply H1.
Qed.

Lemma itr_ext_hrel :
  forall X (R : hrel X X) x y, R x y -> R^+ x y.
Proof.
  intros.
  pose proof itr_ext R. cbn in H0. apply H0. apply H.
Qed.
Hint Resolve itr_ext_hrel : optsim.

#[export] Instance itr_eq X (Eq R : hrel X X) `(EQ : Equivalence _ Eq) :
  Proper (Eq ==> Eq ==> impl) R ->
  Proper (Eq ==> Eq ==> impl) R^+.
Proof.
  intro. cbn -[itr]. intros.
  revert y y0 H0 H1.
  eapply hrel_itr_ind_l' with (P := fun x x0 => forall y y0 : X, Eq x y -> Eq x0 y0 -> R^+ y y0).
  3: apply H2.
  - intros. apply itr_ext_hrel. now rewrite <- H1, <- H3.
  - intros. apply (itr_str_l (X := hrel_monoid_ops)).
    esplit.
    + rewrite <- H3. apply H0.
    + apply (str_itr' (X := hrel_monoid_ops)). now apply H1.
Qed.

Module SimOpt.

  Variant freeze_opt := freeze_div | freeze | nofreeze.
  Variant lock_opt := lock | nolock.
  Variant delay_opt := delay | nodelay.

End SimOpt.
