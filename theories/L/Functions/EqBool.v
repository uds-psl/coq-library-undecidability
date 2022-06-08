From Undecidability.L Require Import L Tactics.LTactics LBool.

Class eqbClass X (eqb : X -> X -> bool): Type := 
  _eqb_spec : forall (x y:X), reflect (x=y) (eqb x y).

#[export] Hint Mode eqbClass + -: typeclass_instances. (* treat argument as input and force evar-freeness*)

Definition eqb X eqb `{H:eqbClass (X:=X) eqb} := eqb.

Arguments eqb {_ _ _}: simpl never.

Lemma eqb_spec {X} {f : X -> X -> bool} {_:eqbClass f}:
  forall (x y:X), reflect (x=y) (eqb x y).
Proof.
  intros. eapply _eqb_spec.
Qed.

#[global]
Instance eqbBool_inst : eqbClass Bool.eqb.
Proof.
  intros ? ?. eapply iff_reflect. rewrite eqb_true_iff. reflexivity.
Qed.

Class eqbCompT X {R:registered X} eqb {H:eqbClass (X:=X) eqb} :=
  { comp_eqb : computable eqb }.
Arguments eqbCompT _ {_ _ _}.

#[export] Hint Mode eqbCompT + - - -: typeclass_instances.

#[global]
Existing Instance comp_eqb.

#[global]
Instance term_eqb_bool : computable Bool.eqb.
Proof.
  extract.
Qed.
