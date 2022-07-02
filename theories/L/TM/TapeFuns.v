From Undecidability.L.Datatypes Require Import LNat LVector.
From Undecidability.L.Datatypes.List Require Import List_basics List_eqb List_enc.

From Undecidability.L Require Import TM.TMEncoding.

From Undecidability.TM Require Import Util.TM_facts.


Section fix_sig.
  Variable sig : Type.
  Context `{reg_sig : registered sig}.

  Section reg_tapes.

    Global Instance term_tape_move_left' : computable (@tape_move_left' sig).
    Proof.
      extract.
    Qed.

    Global Instance term_tape_move_left : computable (@tape_move_left sig).
    Proof.
      extract.
    Qed.

    Global Instance term_tape_move_right' : computable (@tape_move_right' sig).
    Proof.
      extract.
    Qed.

    Global Instance term_tape_move_right : computable (@tape_move_right sig).
    Proof.
      extract.
    Qed.

    Global Instance term_tape_move : computable (@tape_move sig).
    Proof.
      extract.
    Qed.

    Global Instance term_left : computable (@left sig).
    Proof.
      extract.
    Qed.

    Global Instance term_right : computable (@right sig).
    Proof.
      extract.
    Qed.

    Global Instance term_tape_write : computable (@tape_write sig).
    Proof.
      extract.
    Qed.

    Global Instance term_tapeToList:  computable (@tapeToList sig).  
    Proof.
      extract.
    Qed.

    Global Instance term_sizeOfTape: computable (@sizeOfTape sig).
    Proof.
      extract.
    Qed.

    Import Nat.

    Global Instance term_sizeOfmTapes n:
      computable (@sizeOfmTapes sig n).
    Proof.
      set (f:= (fix sizeOfmTapes acc (ts : list (tape sig)) : nat :=
                  match ts with
                  | [] => acc
                  | t :: ts0 => sizeOfmTapes (Init.Nat.max acc (sizeOfTape t)) ts0
                  end)).
      
      assert (H' : extEq (fun v => f 0 (Vector.to_list v)) (@sizeOfmTapes sig n)).
      { intros x. hnf. unfold sizeOfmTapes. generalize 0.
        induction x using Vector.t_ind;intros acc. cbn. nia.        
        cbn in *. rewrite <- IHx. unfold Vector.to_list. nia.
      }
      assert (computable f).
      { unfold f. extract. }

      eapply computableExt. exact H'.
      extract. 
    Qed.

    Global Instance term_current: computable ((current (Σ:=sig))).
    Proof.
      extract.
    Qed.

    Global Instance term_current_chars n: computable (current_chars (sig:=sig) (n:=n)).
    Proof.
      unfold current_chars.
      extract.
    Qed.

    Global Instance term_doAct: computable (doAct (sig:=sig)).
    Proof.
      extract.
    Qed.

  End reg_tapes.
End fix_sig.

Global
Instance term_loop A `{registered A} :
  computable (@loop A).
Proof.
  extract.
Qed.
