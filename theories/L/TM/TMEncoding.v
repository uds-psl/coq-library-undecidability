From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector.
From Undecidability.L Require Import Functions.EqBool.

From Undecidability.TM.Util Require Import TM_facts.

Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.


Import L_Notations.

(* ** Extraction of Turing Machine interpreter  *)

Import GenEncode.
MetaCoq Run (tmGenEncodeInj "move_enc" move).
#[export] Hint Resolve move_enc_correct : Lrewrite.

Import TM.
Local Notation L := TM.Lmove.
Local Notation R := TM.Rmove.
Local Notation N := TM.Nmove.

Definition move_eqb (m n : move) : bool :=
  match m,n with
    N,N => true
  | L,L => true
  | R,R => true
  | _,_ => false
  end.

Lemma move_eqb_spec x y : reflect (x = y) (move_eqb x y).
Proof.
  destruct x, y;constructor. all:easy.
Qed.


#[global]
Instance eqb_move:
  eqbClass move_eqb.
Proof.
  intros ? ?. eapply move_eqb_spec.
Qed.


#[global]
Instance eqbComp_bool : eqbComp move.
Proof.
  constructor. unfold move_eqb.
  extract.
Qed.

(* *** Encoding Tapes *)
Section reg_tapes.
  Variable sig : Type.
  Context `{reg_sig : encodable sig}.

  Implicit Type (t : TM.tape sig).
  Import GenEncode.
  MetaCoq Run (tmGenEncode "tape_enc" (TM.tape sig)).
  Hint Resolve tape_enc_correct : Lrewrite.

  Global Instance encInj_tape_enc {H : encInj reg_sig} : encInj (encodable_tape_enc).
  Proof. register_inj. Qed. 

  (*Internalize constructors **)

  Global Instance term_leftof : computable (@leftof sig).
  Proof.
    extract constructor.
  Qed.

  Global Instance term_rightof : computable (@rightof sig).
  Proof.
    extract constructor.
  Qed.

  Global Instance term_midtape : computable (@midtape sig).
  Proof.
    extract constructor.
  Qed.
  
End reg_tapes.


Section fix_sig.
  Variable sig : finType.
  Context `{reg_sig : encodable sig}.


  Definition mconfigAsPair {B : finType} {n} (c:mconfig sig B n):= let (x,y) := c in (x,y).

  Global Instance encodable_mconfig (B : finType) `{encodable B} n: encodable (mconfig sig B n).
  Proof using reg_sig.
    eapply (registerAs mconfigAsPair).
  Defined.

  Global Instance term_mconfigAsPair (B : finType) `{encodable B} n: computable (@mconfigAsPair B n).
  Proof.
    apply cast_computable.
  Qed.

  Global Instance term_cstate (B : finType) `{encodable B} n: computable (@cstate sig B n).
  Proof.
    apply computableExt with (x:=fun x => fst (mconfigAsPair x)).
    2:{extract. }
    intros [];reflexivity.
  Qed.

  Global Instance term_ctapes (B : finType) `{encodable B} n: computable (@ctapes sig B n).
  Proof.
    apply computableExt with (x:=fun x => snd (mconfigAsPair x)).
    2:{extract. }
    intros [];reflexivity.
  Qed.

  Global Instance encodable_mk_mconfig (B : finType) `{encodable B} n: computable (@mk_mconfig sig B n).
  Proof.
    computable_casted_result.
    extract.
  Qed.
End fix_sig.

#[export] Hint Resolve tape_enc_correct : Lrewrite.
