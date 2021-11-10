From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector.
From Undecidability.L Require Import Functions.EqBool.

From Undecidability.TM.Util Require Import VectorPrelim TM_facts.

Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.
From Undecidability.TM Require PrettyBounds.SizeBounds.


Import L_Notations.

(* ** Extraction of Turing Machine interpreter  *)

Import GenEncode.
MetaCoq Run (tmGenEncode "move_enc" move).
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
Instance eqbComp_bool : eqbCompT move.
Proof.
  evar (c:nat). exists c. unfold move_eqb.
  unfold enc;cbn.
  extract.
  solverec.
  [c]:exact 3.
  all:unfold c;try lia.
Qed.

(*
Definition move_decode (s : term) : option (move) :=
  match s with
  | lam (lam (lam n)) =>
    match n with
      2 => Some TM.L 
    | 1 => Some TM.R
    | 0 => Some TM.N
    | _ => None
    end
  | _ => None
  end.

Instance decode_move: decodable move.
Proof.
  exists move_decode.
  all:unfold enc at 1. all:cbn.
  -destruct x;reflexivity.
  -destruct t eqn:eq. all:cbn.
   all:repeat let eq := fresh in destruct _ eqn:eq. all:try congruence.
   all:intros ? [= <-]. all:reflexivity.
Defined. (* because instance *) *)

(* *** Encoding Tapes *)
Section reg_tapes.
  Variable sig : Type.
  Context `{reg_sig : registered sig}.

  
  Implicit Type (t : TM.tape sig).
  Import GenEncode.
  MetaCoq Run (tmGenEncode "tape_enc" (TM.tape sig)).
  Hint Resolve tape_enc_correct : Lrewrite.

  (*Internalize constructors **)

  Global Instance term_leftof : computableTime' (@leftof sig) (fun _ _ => (1, fun _ _ => (1,tt))).
  Proof.
    extract constructor.
    solverec.
  Qed.

  Global Instance term_rightof : computableTime' (@rightof sig) (fun _ _ => (1, fun _ _ => (1,tt))).
  Proof.
    extract constructor. solverec.
  Qed.

  Global Instance term_midtape : computableTime' (@midtape sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (1,tt)))).
  Proof.
    extract constructor. solverec.
  Qed.
  
End reg_tapes.


Section fix_sig.
  Variable sig : finType.
  Context `{reg_sig : registered sig}.


  Definition mconfigAsPair {B : finType} {n} (c:mconfig sig B n):= let (x,y) := c in (x,y).

  Global Instance registered_mconfig (B : finType) `{registered B} n: registered (mconfig sig B n).
  Proof using reg_sig.
    eapply (registerAs mconfigAsPair). clear.
    register_inj.
  Defined. (* because registerAs *)

  Global Instance term_mconfigAsPair (B : finType) `{registered B} n: computableTime' (@mconfigAsPair B n) (fun _ _ => (1,tt)).
  Proof.
    apply cast_computableTime.
  Qed.

  Global Instance term_cstate (B : finType) `{registered B} n: computableTime' (@cstate sig B n) (fun _ _ => (7,tt)).
  Proof.
    apply computableTimeExt with (x:=fun x => fst (mconfigAsPair x)).
    2:{extract. solverec. }
    intros [];reflexivity.
  Qed.

  Global Instance term_ctapes (B : finType) `{registered B} n: computableTime' (@ctapes sig B n) (fun _ _ => (7,tt)).
  Proof.
    apply computableTimeExt with (x:=fun x => snd (mconfigAsPair x)).
    2:{extract. solverec. }
    intros [];reflexivity.
  Qed.

  Global Instance registered_mk_mconfig (B : finType) `{registered B} n: computableTime' (@mk_mconfig sig B n) (fun _ _ => (1,fun _ _ => (3,tt))).
  Proof.
    computable_casted_result.
    extract. solverec.
  Qed.
End fix_sig.

#[export] Hint Resolve tape_enc_correct : Lrewrite.

Import PrettyBounds.SizeBounds.

Lemma sizeOfTape_by_size {sig} `{registered sig} (t:(tape sig)) :
  sizeOfTape t <= size (enc t).
Proof.
  change (enc (X:=tape sig)) with (tape_enc (sig:=sig)). unfold tape_enc,sizeOfTape.
  change (match H with
          | @mk_registered _ enc _ _ => enc
          end) with (enc (registered:=H)). change (list_enc (X:=sig)) with (enc (X:=list sig)).
  destruct t. all:cbn [tapeToList length tape_enc size].
  all:rewrite ?app_length,?rev_length. all:cbn [length].
  all:ring_simplify. all:try rewrite !size_list_enc_r. all:try nia.
Qed.

Lemma sizeOfmTapes_by_size {sig} `{registered sig} n (t:tapes sig n) :
  sizeOfmTapes t <= size (enc t).
Proof.
  setoid_rewrite enc_vector_eq. rewrite Lists.size_list.
  erewrite <- sumn_map_le_pointwise with (f1:=fun _ => _). 2:{ intros. setoid_rewrite <- sizeOfTape_by_size. reflexivity. }
  rewrite sizeOfmTapes_max_list_map. unfold MaxList.max_list_map. rewrite max_list_sumn.
  etransitivity. 2:now apply Nat.le_add_r. rewrite vector_to_list_correct. apply sumn_map_le_pointwise. intros. nia.
Qed.
