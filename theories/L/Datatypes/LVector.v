From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat List.List_basics List.List_eqb LFinType.

Require Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.

(* *** Encoding vectors *)

#[global]
Instance register_vector X `{encodable X} n : encodable (Vector.t X n).
Proof.
  apply (registerAs VectorDef.to_list). (*
  intros x. induction x.
  - intros y. pattern y. revert y. eapply VectorDef.case0. cbn. reflexivity.
  - intros y. clear H. revert h x IHx. pattern n, y. revert n y.
    eapply Vector.caseS. intros h n y h0 x IHx [=].
    subst. f_equal. eapply IHx. eassumption. *)
Defined. (*because registerAs*)


Lemma enc_vector_eq X `{encodable X} m (x:Vector.t X m):
  enc x = enc (Vector.to_list x).
Proof.
  reflexivity.
Qed.

#[global]
Instance term_to_list X `{encodable X} n : computable (Vector.to_list (A:=X) (n:=n)).
Proof.
  apply cast_computable.
Qed.

Import Vector.
#[global]
Instance term_vector_map X Y `{encodable X} `{encodable Y} n (f:X->Y) :
  computable f ->
  computable (VectorDef.map f (n:=n)).
Proof.
  intros ?.
  computable_casted_result.
  apply computableExt with (x:= fun x => List.map f (Vector.to_list x)).
  2:{
    extract.
  }

  cbn. intros x.
  clear - x.
  induction n. revert x. apply VectorDef.case0. easy. revert IHn. apply Vector.caseS' with (v:=x).
  intros. cbn. f_equal. fold (Vector.fold_right (A:=X) (B:=Y)).
  setoid_rewrite IHn. reflexivity.
Qed.

Global
Instance term_map2 n A B C `{encodable A} `{encodable B} `{encodable C} (g:A -> B -> C) :
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
Instance term_vector_eqb X `{encodable X} (n' m:nat) (eqb:X->X->bool) :
  computable eqb ->
  computable (VectorEq.eqb eqb (A:=X) (n:=n') (m:=m)).
Proof.
  intros ?.
  apply computableExt with (x:=(fun x y => list_eqb eqb (Vector.to_list x) (Vector.to_list y))).
  2:{extract. }
  intros v v'. hnf.
  induction v in n',v'|-*;cbn;destruct v';cbn;try tauto. rewrite <- IHv. f_equal.
Qed.

From Undecidability.L Require Import Functions.EqBool.

Global Instance eqbVector  X eqbx `{eqbClass (X:=X) eqbx} n:
  eqbClass (VectorEq.eqb eqbx (n:=n) (m:=n)).
Proof.
  intros ? ?. apply iff_reflect. symmetry. apply Vector.eqb_eq. symmetry. apply reflect_iff. eauto.
Qed.

Global Instance eqbComp_List X `{encodable X} `{eqbComp X (R:=_)} n:
  eqbComp (Vector.t X n).
Proof.
  constructor. apply term_vector_eqb.
  apply comp_eqb.
Qed.
