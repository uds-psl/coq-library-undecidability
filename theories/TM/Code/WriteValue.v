Require Import CodeTM.
Require Import Basic.Mono.
Require Import TM.Compound.WriteString.
Require Import TMTac.

(* TODO: ~> Base *)

Lemma tl_eq (X : Type) (xs : list X) :
  tl xs = match xs with
          | nil => nil
          | _ :: xs' => xs'
          end.
Proof. reflexivity. Qed.

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
  tape_local (WriteString_Fun L t str) = rev str ++ right t.
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
  Compute WriteString_Fun L t str.
  Compute (left t).
  Compute (left (WriteString_Fun L t str)).
  Compute (skipn (length str - 1) (left t)).
End Test.
*)

Lemma WriteString_L_left (sig : Type) (str : list sig) t :
  left (WriteString_Fun L t str) = skipn (pred (length str)) (left t).
Proof.
  revert t. induction str as [ | s [ | s' str'] IH]; intros; cbn -[skipn] in *.
  - reflexivity.
  - reflexivity.
  - rewrite IH. simpl_tape. now rewrite skipn_S, skipn_tl.
Qed.


  

Lemma tape_local_contains (sig sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) t :
  tape_local t = inl START :: map inr (Encode_map _ _ x) ++ [inl STOP] ->
  t ≃ x.
Proof. intros -> % midtape_tape_local_cons. repeat econstructor. Qed.

Lemma tape_contains_size_strengthen (sig sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (s : nat) (t : tape (boundary + sig)) :
  t ≃ x ->
  length (left t) <= s ->
  t ≃(;s) x.
Proof. intros (rs&->). cbn. intros. hnf. eexists. split; auto. Qed.

Lemma tape_local_contains_size (sig sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (s : nat) (t : tape (boundary + sig)) :
  tape_local t = inl START :: map inr (Encode_map _ _ x) ++ [inl STOP] ->
  length (left t) <= s ->
  t ≃(;s) x.
Proof.
  intros. apply tape_contains_size_strengthen.
  - now eapply tape_local_contains.
  - auto.
Qed.


Arguments WriteString_Fun : simpl never.

Section WriteValue.

  Variable (sig: finType) (X: Type) (cX: codable sig X).

  Definition WriteValue (str : list sig) : pTM sig^+ unit 1 :=
    WriteString L (rev (inl START :: map inr str ++ [inl STOP])).

  Definition WriteValue_size (sig:Type) (cX: codable sig X) (x : X) (s : nat) : nat := s - (S (size _ x)).

  Definition WriteValue_Rel (str : list sig) : Rel (tapes sig^+ 1) (unit * tapes sig^+ 1) :=
    fun tin '(_, tout) =>
      forall (x:X) (s0:nat),
        encode x = str ->
        isRight_size tin[@Fin0] s0 ->
        tout[@Fin0] ≃(;WriteValue_size cX x s0) x.

  Definition WriteValue_steps (l : nat) := 3 + 2 * l.
  
  Lemma WriteValue_Sem (str : list sig) :
    WriteValue str ⊨c(WriteValue_steps (length str)) WriteValue_Rel str.
  Proof.
    unfold WriteValue_steps. eapply RealiseIn_monotone.
    { unfold WriteValue. eapply WriteString_Sem. }
    { unfold WriteString_steps. rewrite !rev_length. cbn [length]. rewrite app_length.
      unfold size. cbn. rewrite map_length. omega. }
    {
      intros tin ((), tout) H. intros x s0 <- (m&(rs&HRight&Hs)).
      unfold WriteValue_size in *.
      TMSimp; clear_trivial_eqs.
      eapply tape_local_contains_size. rewrite WriteString_L_local.
      - rewrite Encode_map_id. rewrite rev_app_distr, <- !app_assoc, rev_involutive, <- !app_assoc. cbn. f_equal.
      - rewrite rev_app_distr, <- !app_assoc. cbn. congruence.
      - rewrite WriteString_L_left. simpl_list; cbn. rewrite skipn_length. unfold size. omega.
    }
  Qed.

End WriteValue.

Arguments WriteValue_size {X sig cX}.


Ltac smpl_TM_WriteValue :=
  lazymatch goal with
  | [ |- WriteValue _ ⊨ _ ] => eapply RealiseIn_Realise; apply WriteValue_Sem
  | [ |- WriteValue _ ⊨c(_) _ ] => apply WriteValue_Sem
  | [ |- projT1 (WriteValue _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply WriteValue_Sem
  end.

Smpl Add smpl_TM_WriteValue : TM_Correct.
