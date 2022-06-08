From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat LFinType.
From Undecidability.L.Datatypes.List Require Import List_basics List_eqb List_fold List_enc.

Require Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.

(* *** Encoding vectors *)

#[global]
Instance register_vector X `{registered X} n : registered (Vector.t X n).
Proof.
  apply (registerAs VectorDef.to_list).
  intros x. induction x.
  - intros y. pattern y. revert y. eapply VectorDef.case0. cbn. reflexivity.
  - intros y. clear H. revert h x IHx. pattern n, y. revert n y.
    eapply Vector.caseS. intros h n y h0 x IHx [=].
    subst. f_equal. eapply IHx. eassumption.
Defined. (*because registerAs*)

#[global]
Instance term_to_list X `{registered X} n : computable (Vector.to_list (A:=X) (n:=n)).
Proof.
  apply cast_computable.
Qed.

Import Vector.
#[global]
Instance term_vector_map X Y `{registered X} `{registered Y} n (f:X->Y):
  computable f ->
  computable (VectorDef.map f (n:=n)).
Proof.
  intros ?.
  computable_casted_result.
  apply computableExt with (x:= fun x => List.map f (Vector.to_list x)).
  2:{extract. }
  cbn. intros x. now rewrite VectorSpec.to_list_map.
Qed.

Global
Instance term_map2 n A B C `{registered A} `{registered B} `{registered C} (g:A -> B -> C):
  computable g -> computable (Vector.map2 g (n:=n)).
Proof.
  intros ?.
  computable_casted_result.
  pose (f:=(fix f t a : list C:=
              match t,a with
                t1::t,a1::a => g t1 a1 :: f t a
              | _,_ => []
              end)).
  assert (computable f).
  {subst f; extract. }

  apply computableExt with (x:= fun t a => f (Vector.to_list t) (Vector.to_list a)).
  2:{extract. }
  induction n;cbn.
  -do 2 destruct x using Vector.case0. reflexivity.
  -destruct x using Vector.caseS'. destruct x0 using Vector.caseS'.
   cbn. f_equal. apply IHn.
Qed.


#[global]
Instance term_vector_eqb X `{registered X} (n' m:nat) (eqb:X->X->bool):
  computable eqb
  -> computable
      (VectorEq.eqb eqb (A:=X) (n:=n') (m:=m)).
Proof.
  intros ?.
  apply computableExt with (x:=(fun x y => list_eqb eqb (Vector.to_list x) (Vector.to_list y))).
  2:{extract. }
  intros v v'. hnf.
  induction v in n',v'|-*;cbn;destruct v';cbn;try tauto. rewrite <- IHv. f_equal.
Qed.

From Undecidability.L Require Import Functions.EqBool.

Global Instance eqbVector X eqbx `{eqbClass (X:=X) eqbx} n:
  eqbClass (VectorEq.eqb eqbx (n:=n) (m:=n)).
Proof.
  intros ? ?. eapply vector_eqb_spec. all:eauto using eqb_spec.
Qed.
