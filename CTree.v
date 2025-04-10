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
From CTree Require Import CTree Eq.
From OptSim Require Import OptSim.

Variant olabel {E} :=
| oobs {X} : E X -> X -> olabel
| oval {X} : X -> olabel.

Definition clabel {E} (l : @OptSim.label (@olabel E)) :=
  match l with
  | tau => τ
  | OptSim.obs (oobs e x) => Trans.obs e x
  | OptSim.obs (oval v) => val v
  end.

Program Definition lts {E B X} : LTS :=
{|
  Observable := @olabel E;
  St := @SS E B X;
  OptSim.trans := fun l => {| hrel_of := Trans.trans (clabel l) |};
  epsilon := {| hrel_of := fun _ _ => False |};
  Robs := eq;
  ub_state := fun _ => False
|}.

Import CTreeNotations.
CoFixpoint t : ctree void1 B2 bool := brS2 t (branchS branch2).
CoFixpoint u : ctree void1 B2 bool := r <- branchS branch2;; brS2 u (Ret r).

Lemma unfold_t : t = brS2 t (branchS branch2). Admitted.
Lemma unfold_u : u = r <- branchS branch2;; brS2 u (Ret r). Admitted.

Goal sim lts SimOpt.div SimOpt.nolock SimOpt.expand t u.
Proof.
  red. coinduction R CH.
  rewrite unfold_t, unfold_u.
  cbn. constructor. repeat split; intros.
  1, 3: admit.
  apply tau_div. reflexivity.
  cbn in H. apply trans_brS_inv in H as (? & ? & _).
  rewrite H. destruct x.
Abort.

Goal gfp (divsimF lts SimOpt.nolock) t u.
Proof.
  coinduction R CH.
  repeat split; intros.
  1, 4: admit.
  - (*cbn -[str] in H. eapply srel_str_ind_l' with (i := trans τ) (P := fun t s' => exists t' : St lts, (OptSim.trans lts tau)^* u t' /\ ` R s' t').
    4: apply H.
    + cbn. intros. subs. admit.
    + intros. *)
   assert (s' = t \/ s' = branchS branch2 \/ s' = Ret true \/ s' = Ret false) by admit.
   destruct H0 as [|[|[|]]]; subst.
   + exists u. split; auto. rewrite <- str_refl. reflexivity.
   + exists u. split; auto. now rewrite <- str_refl. admit.
   + exists (Ret true). split. rewrite str_unfold_l. right. rewrite <- str_ext. cbn. rewrite unfold_u. red. eexists. unfold branchS. rewrite bind_br. eapply trans_br. 2: reflexivity.
     rewrite bind_step. apply trans_step. rewrite bind_ret_l. apply trans_brS22. admit.
   + admit.
 - admit.
Admitted.