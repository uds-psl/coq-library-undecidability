From Undecidability.L.Datatypes Require Import LBool List.List_nat.
From Undecidability.L Require Import TM.TMEncoding.
From Undecidability.TM Require Import Util.TM_facts.

Section fix_sig.
  Variable sig : Type.
  Context `{reg_sig : encodable sig}.

  Section reg_tapes.

    #[export] Instance term_tape_move_left' : computable (@tape_move_left' sig).
    Proof.
      extract.
    Qed.

    #[export] Instance term_tape_move_left : computable (@tape_move_left sig).
    Proof.
      extract.
    Qed.

    #[export] Instance term_tape_move_right' : computable (@tape_move_right' sig).
    Proof.
      extract.
    Qed.

    #[export] Instance term_tape_move_right : computable (@tape_move_right sig).
    Proof.
      extract.
    Qed.

    #[export] Instance term_tape_move : computable (@tape_move sig).
    Proof.
      extract.
    Qed.

    #[export] Instance term_left : computable (@left sig).
    Proof.
      extract.
    Qed.

    #[export] Instance term_right : computable (@right sig).
    Proof.
      extract.
    Qed.

    #[export] Instance term_tape_write : computable (@tape_write sig).
    Proof.
      extract.
    Qed.

    #[export] Instance term_tapeToList:  computable (@tapeToList sig).  
    Proof.
    extract.
    Qed.

    #[export] Instance term_sizeOfTape: computable (@sizeOfTape sig).
    Proof.
      extract.
    Qed.

    Import Nat.

    #[export] Instance term_current: computable ((current (Σ:=sig))).
    Proof.
      extract.
    Qed.

    #[export] Instance term_current_chars n: computable (current_chars (sig:=sig) (n:=n)).
    Proof.
      extract.
    Qed.

    #[export] Instance term_doAct: computable (doAct (sig:=sig)).
    Proof.
      extract.
    Qed.


  End reg_tapes.
End fix_sig.

#[export]
Instance term_loop A `{encodable A} :
  computable (@loop A).
Proof.
  extract.
Qed.
