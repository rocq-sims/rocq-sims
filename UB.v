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

Definition RUB {lts} (R : relation lts.(Observable)) o o' :=
  match o, o' with
  | Some o, Some o' => R o o'
  | _, None => True
  | _, _ => False
  end.

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

End WithLTS.
