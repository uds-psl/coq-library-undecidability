From Undecidability Require Import TM.Util.TM_facts TM.Basic.Mono TM.Combinators.Combinators TM.Compound.Multi.
Require Import List.
From Undecidability Require Import TMTac.
From Coq Require Import List.

(* Useful for running time stuff *)
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


(* The correctness and definition of [WriteString] is non-standard, because it is defined (and verified) by recursion (or induction). *)
Section Write_String.

  Variable sig : finType.
  Variable D : move.

  Fixpoint WriteString (l : list sig) : pTM sig unit 1 :=
    match l with
    | [] => Nop
    | [x] => Write x
    | x :: xs => WriteMove x D;; WriteString xs
    end.

  Fixpoint WriteString_Fun (sig' : Type) (t : tape sig') (str : list sig') :=
    match str with
    | nil => t
    | [x] => tape_write t (Some x)
    | x :: str' => WriteString_Fun (doAct t (Some x, D)) str'
    end.

  Lemma WriteString_Fun_eq (sig' : Type) (t : tape sig') (str : list sig') :
    WriteString_Fun t str =
    match str with
    | nil => t
    | [x] => tape_write t (Some x)
    | x :: str' => WriteString_Fun (doAct t (Some x, D)) str'
    end.
  Proof. destruct str; auto. Qed.

  Lemma Write_String_nil (sig' : Type) (t : tape sig') :
    WriteString_Fun t nil = t.
  Proof. destruct t; cbn; auto. Qed.

  Fixpoint WriteString_sem_fix (str : list sig) : pRel sig unit 1 :=
    match str with
    | nil => Nop_Rel
    | [x] => Write_Rel x
    | x :: str' =>
      WriteMove_Rel x D |_tt ∘ WriteString_sem_fix str'
    end.

  Definition WriteString_steps l :=
    2 * l - 1.
    
  Lemma WriteString_fix_Sem (str : list sig) :
    WriteString str ⊨c(WriteString_steps (length str)) (WriteString_sem_fix str).
  Proof.
    induction str as [ | s [ | s' str'] IH ].
    - cbn. change (2 * 0 - 1) with 0. TM_Correct.
    - cbn. change (2 * 1 - 1) with 1. TM_Correct.
    - change (WriteString (s :: s' :: str')) with (WriteMove s D;; WriteString (s' :: str')).
      eapply RealiseIn_monotone.
      { TM_Correct. TM_Correct. apply IH. }
      { unfold WriteString_steps. cbn. lia. }
      { intros t1 t3 H. destruct H as (()&t2&H1&H2).
        change (WriteString_sem_fix (s :: s' :: str')) with (WriteMove_Rel s D |_tt ∘ WriteString_sem_fix (s' :: str')).
        exists t2. split; auto.
      }
  Qed.
  

  Definition WriteString_Rel str : Rel (tapes sig 1) (unit * tapes sig 1) :=
    Mono.Mk_R_p (ignoreParam (fun tin tout => tout = WriteString_Fun tin str)).

  Lemma WriteString_Sem str :
    WriteString str ⊨c(WriteString_steps (length str)) (WriteString_Rel str).
  Proof.
    eapply RealiseIn_monotone.
    { apply WriteString_fix_Sem. }
    { reflexivity. }
    { induction str as [ | s [ | s' str'] IH]; intros tin (yout, tout) H.
      - cbn. now TMSimp.
      - cbn. now TMSimp.
      - change (WriteString_sem_fix (s :: s' :: str')) with ((WriteMove_Rel s D |_tt ∘ WriteString_sem_fix (s' :: str'))) in H.
        destruct H as (tmid&H1&H2). hnf in H1. apply IH in H2.
        (* cbv [WriteString_Rel Mk_R_p ignoreParam].
        change (WriteString_Fun tin[@Fin0] (s :: s' :: str')) with (WriteString_Fun (tape_move_mono tin[@Fin0] (Some s, D)) (s' :: str')). *)
        now TMSimp.
    }
  Qed.

End Write_String.

Arguments WriteString : simpl never.
Arguments WriteString_Rel {sig} (D) (str) x y/.

Lemma skipn_S (X : Type) (xs : list X) (n : nat) :
  skipn (S n) xs = tl (skipn n xs).
Proof.
  revert xs. induction n as [ | n IH]; intros; cbn in *.
  - destruct xs; auto.
  - destruct xs; auto.
Qed.

(*
Compute skipn 3 (tl [1;2;3;4;5;6;7]).
Compute tl (skipn 3 [1;2;3;4;5;6;7]).
*)

Lemma skipn_tl (X : Type) (xs : list X) (n : nat) :
  skipn n (tl xs) = tl (skipn n xs).
Proof.
  revert xs. induction n as [ | n IH]; intros; cbn in *.
  - destruct xs; auto.
  - destruct xs; cbn; auto.
    replace (match xs with
             | [] => []
             | _ :: l => skipn n l
             end)
      with (skipn n (tl xs)); auto.
    destruct xs; cbn; auto. apply skipn_nil.
Qed.


Lemma WriteString_L_local (sig : Type) (str : list sig) t :
  str <> nil ->
  tape_local (WriteString_Fun Lmove t str) = rev str ++ right t.
Proof.
  revert t. induction str as [ | s [ | s' str'] IH]; intros; cbn in *.
  - tauto.
  - reflexivity.
  - rewrite IH. 2: congruence. simpl_tape. rewrite <- !app_assoc. reflexivity.
Qed.

(*
Section Test.
  Let t : tape nat := midtape [3;2;1] 4 [5;6;7].
  Let str := [3;2;1].
  Compute WriteString_Fun Lmove t str.
  Compute (left t).
  Compute (left (WriteString_Fun Lmove t str)).
  Compute (skipn (length str - 1) (left t)).
End Test.
*)

Lemma WriteString_L_left (sig : Type) (str : list sig) t :
  left (WriteString_Fun Lmove t str) = skipn (pred (length str)) (left t).
Proof.
  revert t. induction str as [ | s [ | s' str'] IH]; intros; cbn -[skipn] in *.
  - reflexivity.
  - reflexivity.
  - rewrite IH. simpl_tape. now rewrite skipn_S, skipn_tl.
Qed.

Lemma WriteString_L_right (sig : Type) (str : list sig) t :
   right (WriteString_Fun Lmove t str) = tl (rev str) ++ right t.
Proof.
  revert t. induction str as [ | s [ | s' str'] IH]; intros; cbn in *.
  - tauto.
  - reflexivity.
  - rewrite IH. simpl_tape. rewrite tl_app with (ys:=[s]),<- !app_assoc. reflexivity. intros (?&[=])%app_eq_nil.
Qed.

Lemma WriteString_L_current (sig : Type) (str : list sig) t :
   current (WriteString_Fun Lmove t str) = hd None (map Some (rev str ++ tape_local t)).
Proof.
  revert t. induction str as [ | s [ | s' str'] IH]; intros; cbn in *.
  - now destruct t.
  - reflexivity.
  - rewrite IH. autorewrite with list. setoid_rewrite app_assoc at 1 2.
    cbn. now destruct (map Some (rev str')); cbn.
Qed.
