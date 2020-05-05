From Undecidability Require Import TM.Code.ProgrammingTools.
From Undecidability Require Import TM.Code.CaseNat.


(** * Machines that compte natural functions *)

(* Don't simplify [skipn (S n) xs]; only, if the number and the lists are constructors *)
Local Arguments skipn { A } !n !l.

Local Arguments Encode_nat : simpl never.


(*
Lemma nat_encode_length (n : nat) :
| encode n : list bool | = S n.
Proof. induction n; cbn; auto. Qed.


Lemma max_plus_minus_le (m n : nat) :
  n + (m - n) <= max m n.
Proof.
  assert (m <= n \/ n <= m) as [H|H] by omega.
  - rewrite <- Nat.le_max_r. omega.
  - rewrite <- Nat.le_max_l. omega.
Qed.

Lemma max_max_le (m n : nat) :
  max (max m n) n = max m n.
Proof.
  assert (m <= n \/ n <= m) as [H|H] by omega.
  - erewrite Nat.max_r.
    + symmetry. now eapply max_r.
    + eapply Nat.eq_le_incl. now eapply max_r.
  - erewrite Nat.max_l.
    + reflexivity.
    + apply Nat.le_max_r.
Qed.
*)


(** ** Addition *)


(*
 * Step machine
 *
 * if (b--) {
 *   a++;
 *   continue;
 * } else {
 *   break;
 * }
 *
 * Tapes:
 * t0: a
 * t1: b
 *)
Definition Add_Step : pTM sigNat^+ (option unit) 2 :=
  If (LiftTapes CaseNat [|Fin1|])
     (Return (LiftTapes Constr_S [|Fin0|]) None)
     (Return Nop (Some tt)).


Definition Add_Loop : pTM sigNat^+ unit 2 := While Add_Step.

(*
 * Full machine in pseudocode:
 * a := n
 * b := m
 * while (b--) { // Loop
 *   a++;
 * }
 * reset b;
 * return a;
 *
 * Tapes:
 * INP t0: m
 * INP t1: n
 * OUT t2: a
 * INT t3: b
 *)
(* Everything, but not reset *)
Definition Add_Main : pTM sigNat^+ unit 4 :=
  LiftTapes (CopyValue _) [|Fin1; Fin2|];; (* copy n to a *)
  LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* copy m to b *)
  LiftTapes Add_Loop [|Fin2; Fin3|]. (* Main loop *)


(*
 * Finally, reset tape b.
 * For technical reasons, it is convienient to define the machine for this last step seperately,
 * because it makes prooving the termination easier.
 *)
Definition Add :=
  Add_Main;; (* Initialisation and main loop *)
  LiftTapes (Reset _) [|Fin3|]. (* Reset b *)


(** *** Correctness of [Add] *)

Definition Add_Step_Rel : pRel sigNat^+ (option unit) 2 :=
  fun tin '(yout, tout) =>
    forall a b sa sb,
      tin [@Fin0] ≃(;sa) a ->
      tin [@Fin1] ≃(;sb) b ->
      match yout, b with
      | Some tt, O => (* break *)
        tout[@Fin0] ≃(;sa) a /\
        tout[@Fin1] ≃(;sb) b
      | None, S b' =>
        tout[@Fin0] ≃(;pred sa) S a /\
        tout[@Fin1] ≃(;S sb) b'
      | _, _ => False
      end.

Lemma Add_Step_Sem : Add_Step ⊨c(9) Add_Step_Rel.
Proof.
  eapply RealiseIn_monotone.
  {
    unfold Add_Step. TM_Correct.
  }
  { cbn. reflexivity. }
  {
    intros tin (yout, tout) H. cbn. intros a b sa sb HEncA HEncB. cbn in *.
    destruct H; TMSimp; clear_trivial_eqs.
    - modpon H. destruct b; auto.
    - modpon H. destruct b; auto.
  }
Qed.


Definition Add_Loop_Rel : pRel sigNat^+ unit 2 :=
  ignoreParam (
      fun tin tout =>
        forall a b sa sb,
          tin [@Fin0] ≃(;sa) a ->
          tin [@Fin1] ≃(;sb) b ->
          tout[@Fin0] ≃(;sa-b) b + a /\
          tout[@Fin1] ≃(;sb+b) 0
    ).

Lemma Add_Loop_Realise : Add_Loop ⊨ Add_Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Add_Loop. TM_Correct. eapply RealiseIn_Realise. apply Add_Step_Sem. }
  {
    apply WhileInduction; intros; intros a b sa sb HEncA HEncB; cbn in *; destruct_unit.
    - modpon HLastStep. destruct b; auto; modpon HLastStep. auto.
    - modpon HStar. destruct b; auto. destruct HStar as (HStar1&HStar2).
      modpon HLastStep. split; auto. contains_ext. f_equal. omega.
  }
Qed.



(* Everything, but reset *)
Definition Add_Main_Rel : pRel sigNat^+ unit 4 :=
  ignoreParam (
      fun tin tout =>
        forall m n sm sn s2 s3,
          tin [@Fin0] ≃(;sm) m ->
          tin [@Fin1] ≃(;sn) n ->
          isVoid_size tin[@Fin2] s2 ->
          isVoid_size tin[@Fin3] s3 ->
          tout[@Fin0] ≃(;sm) m /\
          tout[@Fin1] ≃(;sn) n /\
          tout[@Fin2] ≃(; s2 - (S (size _ n)) - m) m + n /\
          tout[@Fin3] ≃(; s3 - (2 + m) + m) 0
    ).


Lemma Add_Main_Realise : Add_Main ⊨ Add_Main_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Add_Main. TM_Correct.
    - apply CopyValue_Realise with (X := nat).
    - apply CopyValue_Realise with (X := nat).
    - apply Add_Loop_Realise.
  }
  {
    intros tin ((), tout) H. cbn. intros m n sm sn s2 s3 HEncM HEncN HOut HInt.
    TMSimp.
    modpon H. modpon H0. modpon H1.
    repeat split; auto.
    { contains_ext. unfold CopyValue_size. rewrite Encode_nat_hasSize. omega. }
  }
Qed.


Goal forall (x m : nat), x - m + m >= x. intros. omega. Qed.

Definition Add_space2 (m n : nat) (so : nat) := so + m - n - 2.
Definition Add_space3 (m : nat) (s3 : nat) := 2 + (s3 - (2 + m) + m).

Definition Add_Rel : pRel sigNat^+ unit 4 :=
  ignoreParam
    (fun tin tout =>
       forall (m : nat) (n : nat) (sx sy so s3 : nat),
         tin[@Fin0] ≃(;sx) m ->
         tin[@Fin1] ≃(;sy) n ->
         isVoid_size tin[@Fin2] so ->
         isVoid_size tin[@Fin3] s3 ->
         tout[@Fin0] ≃(;sx) m /\ (* First input value stayes unchanged *)
         tout[@Fin1] ≃(;sy) n /\ (* Second input value stayes unchanged *)
         tout[@Fin2] ≃(;Add_space2 m n so) (m + n) /\
         isVoid_size tout[@Fin3] (Add_space3 m s3)
    ).

Lemma Add_Computes : Add ⊨ Add_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Add. TM_Correct.
    - apply Add_Main_Realise.
    - apply Reset_Realise with (X := nat). (* Don't forget the type here! *)
  }
  {
    intros tin ((), tout) H. intros m n sx sy so s3 HEncM HEncN HOut HRight3. TMSimp.
    unfold Add_space2, Add_space3.
    rename H into HMain, H0 into HReset.
    modpon HMain. modpon HReset.
    repeat split; eauto.
    contains_ext. rewrite Encode_nat_hasSize. omega.
  }
Qed.


(** *** Termination of [Add] *)

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Definition Add_Loop_steps b := 9 + 10 * b.

Lemma Add_Loop_Terminates :
  projT1 Add_Loop ↓
         (fun tin i => exists a b,
              tin[@Fin0] ≃ a /\
              tin[@Fin1] ≃ b /\
              Add_Loop_steps b <= i).
Proof.
  eapply TerminatesIn_monotone.
  { unfold Add_Loop. TM_Correct.
    - eapply RealiseIn_Realise. apply Add_Step_Sem.
    - eapply RealiseIn_TerminatesIn. apply Add_Step_Sem. }
  {
    unfold Add_Loop_steps. apply WhileCoInduction. intros tin i (a&b&HEncA&HEncB&Hi).
    destruct b.
    (* (* In case I want to use the [WhileInduction] principle without [match] *)
    - exists 11. repeat split.
      + omega.
      + intros () ? _. omega.
      + intros tmid H. cbn in *. specialize (H _ _ HEncA HEncB). cbn in *. auto.
    - exists 11. repeat split.
      + omega.
      + intros () tmid H. cbn in H. specialize (H _ _ HEncA HEncB). now cbn in *.
      + intros tmid H. cbn in H. specialize (H _ _ HEncA HEncB). cbn in *. destruct H as (H1&H2).
        exists (11 + b * 12). repeat split.
        * exists (S a), b. repeat split; eauto. omega.
        * omega.
        *)
    - exists 9. repeat split.
      + omega.
      + intros o tmid H. cbn in H. modpon H. destruct o; auto.
    - exists 9. repeat split.
      + omega.
      + intros o tmid H. cbn in H. modpon H. cbn -[plus mult] in *.
        destruct o as [ () | ]; auto. destruct H.
        exists (9 + b * 10). repeat split.
        * do 2 eexists. repeat split; eauto. omega.
        * omega.
  }
Qed.


Definition Add_Main_steps m n := 85 + 12 * n + 22 * m.
(* [37 + 12 * n] for [CopyValue] (n) *)
(* [37 + 12 * m] for [CopyValue] (m) *)
(* [9 + 10 * m] for [Add_Loop] *)

Definition Add_Main_T : tRel sigNat^+ 4 := fun tin k => exists m n, tin[@Fin0] ≃ m /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\ Add_Main_steps m n <= k.

Lemma Add_Main_Terminates :
  projT1 Add_Main ↓ Add_Main_T.
Proof.
  unfold Add_Main, Add_Main_steps. eapply TerminatesIn_monotone.
  {
    TM_Correct.
    - apply CopyValue_Realise with (X := nat).
    - apply CopyValue_Terminates with (X := nat).
    - apply CopyValue_Realise with (X := nat).
    - apply CopyValue_Terminates with (X := nat).
    - apply Add_Loop_Terminates.
  }
  {
    intros tin k (m&n&HEncM&HEncN&HOut&HRight3&Hk).
    unfold Add_Main_steps in *.
    exists (37 + 12 * n), (47 + 22 * m). repeat split; cbn.
    - cbn. exists n. split; eauto. unfold CopyValue_steps. rewrite Encode_nat_hasSize. omega.
    - omega.
    - intros tmid ymid. intros (H1&H2). TMSimp.
      modpon H1.
      exists (37 + 12 * m), (Add_Loop_steps m). repeat split.
      + exists m. split. eauto. unfold CopyValue_steps. rewrite Encode_nat_hasSize. omega.
      + unfold Add_Loop_steps. omega.
      + intros tmid2 () (HComp & HInj). TMSimp.
        modpon HComp.
        do 2 eexists; repeat split; eauto; do 2 eexists; eassumption.
  }
Qed.


Definition Add_steps m n := 98 + 12 * n + 22 * m.
(* Additional [12] steps for [Reset], and [1] for [Seq] *)

Definition Add_T : tRel sigNat^+ 4 := fun tin k => exists m n, tin[@Fin0] ≃ m /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\ Add_steps m n <= k.

Lemma Add_Terminates :
  projT1 Add ↓ Add_T.
Proof.
  unfold Add, Add_steps. eapply TerminatesIn_monotone.
  {
    TM_Correct.
    - apply Add_Main_Realise.
    - apply Add_Main_Terminates.
    - apply Reset_Terminates with (X := nat).
  }
  {
    intros tin k (m&n&HEncM&HEncN&HOut&HInt&Hk).
    exists (Add_Main_steps m n), 12. repeat split.
    - cbn. exists m, n. repeat split; eauto.
    - unfold Add_Main_steps. unfold Add_steps in *. omega.
    - intros tmid () HComp. cbn in *.
      modpon HComp.
      exists 0. split. eauto. unfold MoveRight_steps. cbn. auto.
  }
Qed.



(** ** Multiplication *)


(*
 * Complete Machine:
 *
 * INP t0: m
 * INP t1: n  (for Add: INP t0)
 * OUT t2: c  (for Add: INP t1)
 * INT t3: c' (for Add: OUT t2)
 * INT t4:    (for Add: INT t3)
 * INT t5: m' (copy of m)
 *
 * Pseudocode:
 * c := 0
 * while (m--) {
 *   ADD(n, c, c')
 *   Reset c
 *   c := c'
 *   Reset c'
 * }
 * Reset m'
 *)

(*
 * Step-Machine:
 * (Note that it only accesses the copy of m)
 *
 * t0: m' (counter)
 * t1: n  (for Add: INP t0)
 * t2: c  (for Add: INP t1)
 * t3: c' (for Add: OUT t2)
 * t4:    (for Add: INT t3)
 *
 * if (m'--) {
 *   Add(n, c, c')
 *   c := c
 *   reset c'
 *   continue
 * } else {
 *   break
 * }
 *)
Definition Mult_Step : pTM sigNat^+ (option unit) 5 :=
  If (LiftTapes CaseNat [|Fin0|])
     (Return (
          LiftTapes Add [|Fin1; Fin2; Fin3; Fin4|];; (* Add(n, c, c') *)
          LiftTapes (MoveValue _) [|Fin3; Fin2|]
        ) (None)) (* continue *)
     (Return Nop (Some tt)). (* break *)


Definition Mult_Loop := While Mult_Step.


(*
 * INP t0: m
 * INP t1: n  (for Mult_Loop: t1)
 * OUT t2: c  (for Mult_Loop: t2)
 * INT t3: c' (for Mult_Loop: t3)
 * INT t4:    (for Mult_Loop: t4)
 * INT t5: m' (for Mult_Loop: t0)
 *)
Definition Mult_Main : pTM sigNat^+ unit 6 :=
  LiftTapes (CopyValue _) [|Fin0; Fin5|];; (* m' := m *)
  LiftTapes (Constr_O) [|Fin2|];; (* c := 0 *)
  LiftTapes Mult_Loop [|Fin5; Fin1; Fin2; Fin3; Fin4|]. (* Main loop *)


Definition Mult : pTM sigNat^+ unit 6 :=
  Mult_Main;;
  LiftTapes (Reset _) [|Fin5|]. (* Reset m' *)


(** *** Correctness of [Mult] *)

Definition Mult_Step_Rel : pRel sigNat^+ (option unit) 5 :=
  fun tin '(yout, tout) =>
    forall (c m' n : nat) (sm sn sc s3 s4 : nat),
      tin[@Fin0] ≃(;sm) m' ->
      tin[@Fin1] ≃(;sn) n ->
      tin[@Fin2] ≃(;sc) c ->
      isVoid_size tin[@Fin3] s3 ->
      isVoid_size tin[@Fin4] s4 ->
      match yout, m' with
      | (Some tt), O => (* return *)
        tout[@Fin0] ≃(;sm) m' /\
        tout[@Fin1] ≃(;sn) n /\
        tout[@Fin2] ≃(;sc) c /\
        isVoid_size tout[@Fin3] s3 /\
        isVoid_size tout[@Fin4] s4
      | None, S m'' => (* continue *)
        tout[@Fin0] ≃(;S sm) m'' /\
        tout[@Fin1] ≃(;sn) n /\
        tout[@Fin2] ≃(;sc-n) n + c /\
        isVoid_size tout[@Fin3] (2 + n + c + Add_space2 n c s3)  /\
        isVoid_size tout[@Fin4] (Add_space3 n s4)
      | _, _ => False
      end.

Lemma Mult_Step_Realise : Mult_Step ⊨ Mult_Step_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Mult_Step. TM_Correct.
    - apply Add_Computes.
    - apply MoveValue_Realise with (X := nat).
  }
  {
    intros tin (yout, tout) H. intros c m' n sm sn sc s3 s4 HEncM' HEncN HEncC HInt3 HInt4. TMSimp.
    destruct H; TMSimp.
    - rename H into HCaseNat, H0 into HAdd, H1 into HMove.
      modpon HCaseNat.
      destruct m' as [ | m']; auto.
      modpon HAdd. modpon HMove.
      repeat split; auto.
      + contains_ext. unfold MoveValue_size_y. rewrite !Encode_nat_hasSize. omega.
      + isVoid_mono. unfold Add_space2. unfold MoveValue_size_x. rewrite Encode_nat_hasSize. omega.
    - modpon H. destruct m' as [ | m']; auto.
  }
Qed.


Fixpoint Mult_Loop_space34 (m' n c : nat) (s3 s4 : nat) { struct m' } : Vector.t nat 2 :=
  match m' with
  | 0 => [| s3; s4 |]
  | S m'' => Mult_Loop_space34 m'' n (n + c) (2 + n + c + Add_space2 n c s3) (Add_space3 n s4)
  end.


Definition Mult_Loop_Rel : pRel sigNat^+ unit 5 :=
  ignoreParam (
      fun tin tout =>
        forall c m' n sm sn sc s3 s4,
          tin[@Fin0] ≃(;sm) m' ->
          tin[@Fin1] ≃(;sn) n ->
          tin[@Fin2] ≃(;sc) c ->
          isVoid_size tin[@Fin3] s3 ->
          isVoid_size tin[@Fin4] s4 ->
          tout[@Fin0] ≃(;sm+m') 0 /\
          tout[@Fin1] ≃(;sn) n /\
          tout[@Fin2] ≃(;sc-m'*n) m' * n + c /\
          isVoid_size tout[@Fin3] (Mult_Loop_space34 m' n c s3 s4)[@Fin0] /\
          isVoid_size tout[@Fin4] (Mult_Loop_space34 m' n c s3 s4)[@Fin1]
    ).


Lemma Mult_Loop_Realise :
  Mult_Loop ⊨ Mult_Loop_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Mult_Loop. TM_Correct. eapply Mult_Step_Realise.
  }
  {
    eapply WhileInduction; intros; intros c m' n sm sn sc s3 s4 HEncM' HEncN HEncC HInt3 HInt4; TMSimp.
    - modpon HLastStep. destruct m' as [ | m']; auto. modpon HLastStep. auto.
    - modpon HStar.
      destruct m' as [ | m']; auto. destruct HStar as (HStar1&HStar2&HStar3&HStar4&HStar5).
      modpon HLastStep.
      rewrite Nat.add_assoc in *. replace (n + m' * n + c) with (m' * n + n + c) by omega.
      repeat split; auto. contains_ext. f_equal. now rewrite Nat.mul_succ_l.
      + rewrite Nat.mul_succ_l. cbn. apply Nat.eq_le_incl. rewrite <- Nat.sub_add_distr; f_equal. omega.
  }
Qed.

(*
 * Complete Machine:
 *
 * INP t0: m
 * INP t1: n  (from Add: INP t0)
 * OUT t2: c  (from Add: INP t1)
 * INT t3: c' (from Add: OUT t2)
 * INT t4:    (from Add: INT t3)
 * INT t5: m' (copy of m)
 *
 * Pseudocode:
 * c := 0
 * m' := m
 * while (m--) {
 *   ADD(n, c, c')
 *   c := c'
 *   reset c'
 * }
 * reset m'
 *)

Definition Mult_Main_Rel : pRel sigNat^+ unit 6 :=
  ignoreParam (
      fun tin tout =>
        forall (m n : nat) (sm sn so s3 s4 s5 : nat),
          tin[@Fin0] ≃(;sm) m ->
          tin[@Fin1] ≃(;sn) n ->
          isVoid_size tin[@Fin2] so ->
          isVoid_size tin[@Fin3] s3 ->
          isVoid_size tin[@Fin4] s4 ->
          isVoid_size tin[@Fin5] s5 ->
          tout[@Fin0] ≃(;sm) m /\
          tout[@Fin1] ≃(;sn) n /\
          tout[@Fin2] ≃(;so-m*n) m * n /\
          isVoid_size tout[@Fin3] ((Mult_Loop_space34 m n 0 s3 s4)[@Fin0]) /\
          isVoid_size tout[@Fin4] ((Mult_Loop_space34 m n 0 s3 s4)[@Fin1]) /\
          tout[@Fin5] ≃(;s5+m) 0
    ).

Lemma Mult_Main_Realise :
  Mult_Main ⊨ Mult_Main_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Mult_Main. TM_Correct.
    - apply CopyValue_Realise with (X := nat).
    - apply Mult_Loop_Realise.
  }
  {
    intros tin ((), tout) H. intros m n sm sn s0 s3 s4 s5 HEncM HEncN Hout HInt3 HInt4 HInt5.
    TMSimp.
    modpon H. modpon H0. modpon H1. rewrite Nat.add_0_r in H4.
    repeat split; eauto.
    { contains_ext. unfold CopyValue_size, Constr_O_size. cbn. omega. }
    { contains_ext. unfold CopyValue_size, Constr_O_size. cbn. omega. }
  }
Qed.


Definition Mult_Rel : pRel sigNat^+ unit 6 :=
  ignoreParam
    (fun tin tout =>
       forall (m : nat) (n : nat) (sm sn so s3 s4 s5 : nat),
         tin[@Fin0] ≃(;sm) m ->
         tin[@Fin1] ≃(;sn) n ->
         isVoid_size tin[@Fin2] so ->
         isVoid_size tin[@Fin3] s3 ->
         isVoid_size tin[@Fin4] s4 ->
         isVoid_size tin[@Fin5] s5 ->
         tout[@Fin0] ≃(;sm) m /\
         tout[@Fin1] ≃(;sn) n /\
         tout[@Fin2] ≃(;so-m*n) m * n /\
         isVoid_size tout[@Fin3] ((Mult_Loop_space34 m n 0 s3 s4)[@Fin0]) /\
         isVoid_size tout[@Fin4] ((Mult_Loop_space34 m n 0 s3 s4)[@Fin1]) /\
         isVoid_size tout[@Fin5] (S (S (m + s5)))
    ).


Lemma Mult_Computes :
  Mult ⊨ Mult_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Mult. TM_Correct.
    - eapply Mult_Main_Realise.
    - eapply Reset_Realise with (X := nat).
  }
  {
    intros tin ((), tout) H. cbn. intros m n sm sn so s3 s4 s5 HEncM HEncN HOut HInt3 HInt4 HInt5. TMSimp.
    rename H into HMain, H0 into HReset.
    modpon HMain. modpon HReset.
    repeat split; auto.
    {  isVoid_mono. unfold Reset_size. rewrite !Encode_nat_hasSize. cbn. omega. }
  }
Qed.


(** *** Termination of Mult *)

Definition Mult_Step_steps m' n c :=
  match m' with
  | O => 6
  | _ => 168 + 33 * c + 39 * n
  end.
(* [5] for [If] and [1] for [CaseNat] *)
(* [98+12*n+22*c] for [Add] *)
(* [12+c] for [Reset] (c) *)
(* [36+12*(c+n)] for [CopyValue] (c' = c + n) *)
(* [12 + (c+n)] for [Reset] (c' = c + n) *)

Lemma Mult_Step_Terminates :
  projT1 Mult_Step ↓
         (fun tin k => exists m' n c,
              tin[@Fin0] ≃ m' /\
              tin[@Fin1] ≃ n /\
              tin[@Fin2] ≃ c /\
              isVoid tin[@Fin3] /\
              isVoid tin[@Fin4] /\
              Mult_Step_steps m' n c <= k).
Proof.
  eapply TerminatesIn_monotone.
  {
    unfold Mult_Step. TM_Correct.
    - apply Add_Computes.
    - apply Add_Terminates.
    - apply MoveValue_Terminates with (X := nat).
  }
  {
    intros tin k. intros (m'&n&c&HEncM'&HEncN&HEncC&HInt3&HInt4&Hk).
    destruct m' as [ | m']; cbn.
    - exists 5, 0. cbn in *; repeat split; eauto.
      intros tmid y (HComp&HInj). TMSimp.
      modpon HComp. destruct y; auto.
    - exists 5, (162 + 33 * c + 39 * n); cbn in *; repeat split; eauto.
      intros tmid y (HComp&HInj). TMSimp.
      modpon HComp. cbn in *. destruct y; auto.
      exists (Add_steps n c), (63 + 21 * c + 17 * n); cbn in *; repeat split.
      do 2 eexists. repeat split; eauto.
      unfold Add_steps. omega.
      intros tmid0 () (HComp2&HInj). TMSimp.
      modpon HComp2.
      do 2 eexists. repeat split; eauto. unfold MoveValue_steps. rewrite !Encode_nat_hasSize. omega.
  }
Qed.


Fixpoint Mult_Loop_steps m' n c :=
  match m' with
  | O => S (Mult_Step_steps m' n c)
  | S m'' => S (Mult_Step_steps m' n c) + Mult_Loop_steps m'' n (n + c)
  end.


Lemma Mult_Loop_Terminates :
  projT1 Mult_Loop ↓
         (fun tin i => exists m' n c,
              tin[@Fin0] ≃ m' /\
              tin[@Fin1] ≃ n /\
              tin[@Fin2] ≃ c /\
              isVoid tin[@Fin3] /\
              isVoid tin[@Fin4] /\
              Mult_Loop_steps m' n c <= i).
Proof.
  eapply TerminatesIn_monotone.
  { unfold Mult_Loop. TM_Correct.
    - apply Mult_Step_Realise.
    - apply Mult_Step_Terminates. }
  {
    apply WhileCoInduction. intros tin k (m'&n&c&HEncM'&HEncN&HEncC&HRight3&HRight4&Hk).
    destruct m' as [ | m''] eqn:E; cbn in *; exists (Mult_Step_steps m' n c).
    {
      repeat split.
      - do 3 eexists. repeat split; eauto. cbn. unfold Mult_Step_steps. destruct m'; omega.
      - intros o tmid H1.
        modpon H1.
        destruct o as [ () | ]; auto. destruct H1 as (HComp1&HComp2&HComp3&HComp4&HComp5).
        subst. cbn. omega.
    }
    {
      repeat split.
      - do 3 eexists. repeat split; eauto. cbn. unfold Mult_Step_steps. destruct m'; omega.
      - intros o tmid H1.
        modpon H1.
        destruct o as [ () | ]; auto. destruct H1 as (HComp1&HComp2&HComp3&HComp4&HComp5).
        cbn. eexists. repeat split.
        + do 3 eexists. repeat split; eauto.
        + cbn. rewrite <- Hk. subst. clear_all. unfold Mult_Step_steps. omega.
    }
  }
Qed.


Definition Mult_Main_steps m n := 44 + 12 * m + Mult_Loop_steps m n 0.
(* [2] steps for [Seq], in total *)
(* [37+12*m] for [CopyValue] (m) *)
(* [Mult_Loop_steps m n 0] for [Mult_Loop] *)



Definition Mult_Main_T : tRel sigNat^+ 6 := fun tin k => exists m n, tin[@Fin0] ≃ m /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ (forall i : Fin.t 3, isVoid tin[@FinR 3 i]) /\ Mult_Main_steps m n <= k.

Lemma Mult_Main_Terminates : projT1 Mult_Main ↓ Mult_Main_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold Mult_Main. TM_Correct.
    - apply CopyValue_Realise with (X := nat).
    - apply CopyValue_Terminates with (X := nat).
    - apply Mult_Loop_Terminates.
  }
  {
    intros tin k (m&n&HEncM&HEncN&HOut&HInt&Hk). cbn in *. unfold Mult_Main_steps in Hk.
    exists (37 + 12 * m), (6 + Mult_Loop_steps m n 0). repeat split; try omega.
    eexists. repeat split; eauto. unfold CopyValue_steps. rewrite Encode_nat_hasSize; cbn. omega.
    intros tmid () (H1&H2); TMSimp.
    specialize (HInt Fin2) as HInt'. modpon H1.
    exists 5, (Mult_Loop_steps m n 0). repeat split; try omega.
    unfold Constr_O_steps. omega.
    intros tmid2 () (H2&HInj2); TMSimp. modpon H2.
    do 3 eexists. repeat split; eauto.
  }
Qed.


Definition Mult_steps m n := 13 + Mult_Main_steps m n.

Definition Mult_T : tRel sigNat^+ 6 := fun tin k => exists m n, tin[@Fin0] ≃ m /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ (forall i : Fin.t 3, isVoid tin[@FinR 3 i]) /\ Mult_steps m n <= k.

Lemma Mult_Terminates : projT1 Mult ↓ Mult_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold Mult. TM_Correct.
    - apply Mult_Main_Realise.
    - apply Mult_Main_Terminates.
    - apply Reset_Terminates with (X := nat).
  }
  {
    intros tin k (m&n&HEncM&HEncN&HOut&HInt&Hk). cbn in *. unfold Mult_steps in Hk.
    exists (Mult_Main_steps m n), 12. repeat split; try omega.
    do 2 eexists; repeat split; eauto.
    intros tmid () H1; TMSimp.
    specialize (HInt Fin0) as HInt0. specialize (HInt Fin1) as HInt4. specialize (HInt Fin2) as HInt5.
    modpon H1.
    exists 0. split; auto.
  }
Qed.
