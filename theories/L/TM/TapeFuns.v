From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector.
From Undecidability.L Require Import TM.TMEncoding.


From Undecidability Require Import TM.TM.
Require Import PslBase.FiniteTypes.FinTypes.


Section fix_sig.
  Variable sig : finType.
  Context `{reg_sig : registered sig}.

  Section reg_tapes.

    Global Instance term_tape_move_left' : computableTime' (@tape_move_left' sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (12,tt)))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_left : computableTime' (@tape_move_left sig) (fun _ _ => (23,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_right' : computableTime' (@tape_move_right' sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (12,tt)))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_right : computableTime' (@tape_move_right sig) (fun _ _ => (23,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move : computableTime' (@tape_move sig) (fun _ _ => (1,fun _ _ => (48,tt))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_left : computableTime' (@left sig) (fun _ _ => (10,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_right : computableTime' (@right sig) (fun _ _ => (10,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_write : computableTime' (@tape_write sig) ((fun _ _ => (1,fun _ _ => (28,tt)))).
    Proof.
      extract. solverec.
    Qed.

  End reg_tapes.
End fix_sig.





