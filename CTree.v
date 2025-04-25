From CTree Require Import CTree Eq.
From OptSim Require Import Utils LTS OptSim.

Import CoindNotations.


Variant olabel {E} :=
| oobs {X} : E X -> X -> olabel
| oval {X} : X -> olabel.

Definition clabel {E} (l : @LTS.label (@olabel E)) :=
  match l with
  | tau => τ
  | LTS.obs (oobs e x) => Trans.obs e x
  | LTS.obs (oval v) => val v
  end.

Program Definition lts {E B X} : LTS :=
{|
  Observable := @olabel E;
  St := @SS E B X;
  LTS.trans := fun l => {| hrel_of := Trans.trans (clabel l) |};
  epsilon := {| hrel_of := fun _ _ => False |};
  Robs := eq;
  ub_state := fun _ => False
|}.

#[export] Instance Chain_simF_equ E B X freeze lock delay b : forall (R : Chain (simF (lts := lts) freeze lock delay)),
  Proper (@equ E B X X eq ==> equ eq ==> impl) (`R b).
Proof.
  intros. cbn. intros.
  eapply (Chain_simF_eq'' (lts := lts)); eauto.
Qed.
