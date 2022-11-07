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

Lemma dec_reflect_remove {P Y} (d:dec P) b (H:reflect P b) (y y' : Y):
  (if d then y else y') = (if b then y else y').
Proof.
  destruct H,d;easy.
Qed.

Lemma eqDec_remove {X Y eqb} {H:eqbClass (X:=X) eqb} x x' (d:dec (x=x')) (a b : Y):
  (if d then a else b) = (if eqb x x' then a else b).
Proof.
  apply dec_reflect_remove. eapply eqb_spec.
Qed.

Class eqbComp X {R:encodable X} eqb {H:eqbClass (X:=X) eqb} :=
  { comp_eqb : computable eqb  }.
Arguments eqbComp _ {_ _ _}.

#[export] Hint Mode eqbComp + - - -: typeclass_instances.

#[global]
Existing Instance comp_eqb.

#[global]
Instance eqbComp_bool : eqbComp bool.
Proof.
  constructor. unfold Bool.eqb.
  extract.
Qed.
