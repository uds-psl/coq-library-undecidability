From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector.
From Undecidability.L Require Import TM.TMEncoding.


From Undecidability Require Import TM.Util.TM_facts.
Require Import PslBase.FiniteTypes.FinTypes.


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


    Import Datatypes.
    Global Instance term_tapeToList:  computableTime' (@tapeToList sig) (fun t _ => (sizeOfTape t*29 + 26,tt)).
    Proof.
      extract. recRel_prettify2. all:repeat (simpl_list;cbn -[plus mult]). all:nia.
    Qed.


    Global Instance term_sizeOfTape: computableTime' (@sizeOfTape sig) (fun t _ => (sizeOfTape t*40 + 35,tt)).
    Proof.
      extract. unfold sizeOfTape. solverec.
    Qed.

    (*MOVE*)
    Lemma Vector_fold_right_to_list (A B : Type) (f : A -> B -> B) (n : nat) (v : Vector.t A n) (a : B):
      Vector.fold_right f v a = fold_right f a (Vector.to_list v).
    Proof. unfold Vector.to_list.
           induction n. all:destruct_vector. all:cbn;congruence.
    Qed.
    Lemma Vector_fold_left_to_list (A B : Type) (f : A -> B -> A) (n : nat) (v : VectorDef.t B n) (a : A):
      VectorDef.fold_left f a v = fold_left f (Vector.to_list v) a.
    Proof. unfold Vector.to_list.
           induction n in v,a|-*. all:destruct_vector. all:cbn;congruence.
    Qed.
    Lemma Vector_map_to_list (A B : Type) (f : A -> B) (n : nat) (v : VectorDef.t A n):
       Vector.to_list (VectorDef.map f v) = map f (Vector.to_list v).
    Proof. unfold Vector.to_list. induction n in v|-*. all:destruct_vector. all:cbn;congruence.
    Qed.

    Import Nat.
    Global Instance term_sizeOfmTapes n:
      computableTime' (@sizeOfmTapes sig n) (fun t _ => ((sizeOfmTapes t*65+61) * n + 16,tt)).
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
      assert (computableTime' f (fun acc _ => (5, fun t _ => ((max acc (fold_right max 0 (map (sizeOfTape (sig:=sig))t))*65 + 61) * (length t) + 9,tt)))).
      { unfold f. extract. solverec. }

      eapply computableTimeExt. exact H'.
      Import Vector.
      extract. solverec. unfold sizeOfmTapes. rewrite Vector_fold_left_to_list,fold_symmetric. 2,3:intros;nia.
      rewrite Vector_map_to_list,to_list_length.
      set (List.fold_right _ _ _). nia. 
    Qed.

    Global Instance term_current: computableTime' ((current (Σ:=sig))) (fun _ _ => (10,tt)).
    Proof.
      extract.
      solverec.
    Qed.

    Global Instance term_current_chars n: computableTime' (current_chars (sig:=sig) (n:=n))  (fun _ _ => (n * 22 +12,tt)).
    Proof.
      extract.
      solverec.
      rewrite map_time_const,to_list_length.  lia.
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

Instance term_loop A `{registered A} :
  computableTime' (@loop A)
                 (fun f fT => (1,fun p pT => (1,fun a _ => (5,fun k _ =>(loopTime f fT p pT a k,tt))))).
Proof.
  extract.
  solverec.
Qed.



