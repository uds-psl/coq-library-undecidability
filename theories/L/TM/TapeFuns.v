From Undecidability.L.Datatypes Require Import LNat Lists LVector.
From Undecidability.L Require Import TM.TMEncoding.

From Undecidability.TM Require Import Util.TM_facts.


Set Default Proof Using "Type".
Section fix_sig.
  Variable sig : Type.
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


    
    Global Instance term_tapeToList:  computableTime' (@tapeToList sig) (fun t _ => (sizeOfTape t*29 + 53,tt)).  
    Proof.
    extract. recRel_prettify2. all:repeat (simpl_list;cbn -[plus mult]). 
    all: unfold c__rev, c__app. all: try nia.
    Qed.


    Global Instance term_sizeOfTape: computableTime' (@sizeOfTape sig) (fun t _ => (sizeOfTape t*40 + 65,tt)).
    Proof.
      extract. unfold sizeOfTape. solverec. unfold c__length. solverec. 
    Qed.

    Import Nat.

    Global Instance term_sizeOfmTapes n:
      computableTime' (@sizeOfmTapes sig n) (fun t _ => ((sizeOfmTapes t*105+101) * n + 56,tt)).
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
      assert (computableTime' f (fun acc _ => (5, fun t _ => ((max acc (fold_right max 0 (map (sizeOfTape (sig:=sig))t))*105 + 101) * (length t) + 49,tt)))).
      { unfold f. extract. solverec. unfold c__max1, max_time, c__max2. solverec. }

      eapply computableTimeExt. exact H'.
      extract. solverec. unfold sizeOfmTapes. rewrite vector_fold_left_to_list,fold_symmetric. 2,3:intros;nia.
      rewrite vector_map_to_list,to_list_length.
      set (List.fold_right _ _ _). nia. 
    Qed.

    Global Instance term_current: computableTime' ((current (Σ:=sig))) (fun _ _ => (10,tt)).
    Proof.
      extract.
      solverec.
    Qed.

    Global Instance term_current_chars n: computableTime' (current_chars (sig:=sig) (n:=n))  (fun _ _ => (n * 22 +16,tt)).
    Proof.
      extract.
      solverec.
      rewrite map_time_const,to_list_length. unfold c__map. lia.
    Qed.

    Global Instance term_doAct: computableTime' (doAct (sig:=sig)) (fun _ _ => (1,fun _ _ => (89,tt))).
    Proof.
      extract.
      solverec.
    Qed.


  End reg_tapes.
End fix_sig.

Fixpoint loopTime {X} `{registered X} f (fT: timeComplexity (X -> X)) (p: X -> bool) (pT : timeComplexity (X -> bool)) (a:X) k :=
  fst (pT a tt) +
  match k with
    0 => 7
  |  S k =>
     fst (fT a tt) + 13 + loopTime f fT p pT (f a) k
  end.

Global
Instance term_loop A `{registered A} :
  computableTime' (@loop A)
                 (fun f fT => (1,fun p pT => (1,fun a _ => (5,fun k _ =>(loopTime f fT p pT a k,tt))))).
Proof.
  extract.
  solverec.
Qed.
