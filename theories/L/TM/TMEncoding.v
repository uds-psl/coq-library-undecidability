From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector.
From Undecidability.L Require Import Computability.MuRec Functions.FinTypeLookup.
From Undecidability.L Require Import MuRec.


From Undecidability Require Import TM.TM L.Functions.Decoding.
Require Import PslBase.FiniteTypes.FinTypes.

(** ** Extraction of Turing Machine interpreter  *)


Run TemplateProgram (tmGenEncode "move_enc" move).
Hint Resolve move_enc_correct : Lrewrite.

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
Defined.*)

(** *** Encoding Tapes *)
Section reg_tapes.
  Variable sig : Type.
  Context `{reg_sig : registered sig}.

  
  Implicit Type (t : TM.tape sig).

  Run TemplateProgram (tmGenEncode "tape_enc" (TM.tape sig)).
  Hint Resolve tape_enc_correct : Lrewrite.

  (**Internalize constructors **)

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


Definition tape_decode X `{decodable X} (s : term) : option (tape X) :=
  match s with
  | lam (lam (lam (lam 3))) => Some (niltape _)
  | lam (lam (lam (lam (app ( app 2 c) r)))) =>
     match decode X c,decode (list X) r with
       Some x, Some xs => Some (leftof x xs)
     | _,_ => None
     end
  | lam (lam (lam (lam (app ( app 1 c) l)))) =>
    match decode X c,decode (list X) l with
      Some x, Some xs => Some (rightof x xs)
    | _,_ => None
    end
  | lam (lam (lam (lam (app ( app (app 0 l) c) r)))) =>
    match decode X c,decode (list X) l,decode (list X) r with
      Some x, Some xs, Some r => Some (midtape xs x r)
    | _,_,_ => None
    end
  | _ => None
  end.

Arguments tape_decode : clear implicits.
Arguments tape_decode _ {_ _} _.

Instance decode_tape X `{registered X} {H:decodable X}: decodable (tape X).
Proof.
  exists (tape_decode X).
  all:unfold enc at 1. all:cbn.
  -destruct x;cbn.
   all:repeat setoid_rewrite decode_correct. all:easy.
  -destruct t eqn:eq. all:cbn.
   all:repeat let eq := fresh in destruct _ eqn:eq. all:try congruence.
   all:intros ? [= <-].
   easy.
   all:cbn.
   all:change (match H with
               | @mk_registered _ enc _ _ => enc
               end x) with (enc x).
   all: change (list_enc (intX:=H)) with (@enc _ _ : list X -> term) in *.
   all: (setoid_rewrite @decode_correct2;[ |try eassumption..]).
   all:easy.
Defined.

Section fix_sig.
  Variable sig : finType.
  Context `{reg_sig : registered sig}.



  Definition mconfigAsPair {B : finType} {n} (c:mconfig sig B n):= let (x,y) := c in (x,y).

  Global Instance registered_mconfig (B : finType) `{registered B} n: registered (mconfig sig B n).
  Proof.
    eapply (registerAs mconfigAsPair). clear.
    register_inj.
  Defined.

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


(* Fixpoint time_loop f fT p pT := cnst 1. *)
Hint Resolve tape_enc_correct : Lrewrite.
