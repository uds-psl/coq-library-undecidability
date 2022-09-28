(*
  (Alternative) Minsky Machine PACK, UNPACK routines
  PACK A X Y offset:
    X := (X+X+1)*(2^Y)
    Y := 0
    A := 0 (auxiliary)
  UNPACK A X Y offset:
    IF X = (n+n+1)*2^m THEN X := n, Y := m, A := 0 (auxiliary)

  Other subprograms:
    INC, DEC, JMP, JZ, ZERO, MOVE, MOVE2, HALF
*)

From Undecidability Require Import
  MinskyMachines.MM MinskyMachines.MMA.

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Require Import PeanoNat List Lia Wf_nat.
Import ListNotations.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

#[local] Arguments ltof /.

Section FixCounters.
Context {num_counters : nat}.
#[local] Notation counter := (pos num_counters).
#[local] Notation mm_instr := (mm_instr counter).
#[local] Notation mm_state := (mm_state num_counters).

#[local] Notation "P // s ->> t" := (sss_compute (@mma_sss num_counters) P s t).
#[local] Notation "P // s -+> t" := (sss_progress (@mma_sss num_counters) P s t).
#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

(* simplify vec_change statements *)
Definition vec_norm {X Y: counter} (HXY : X <> Y) := (
  fun v n m => @vec_change_comm nat _ v X Y n m HXY,
  fun v n m => @vec_change_idem nat _ v X n m,
  fun v n m => @vec_change_idem nat _ v Y n m,
  fun v n => @vec_change_neq nat _ v X Y n HXY,
  fun v n => @vec_change_neq nat _ v Y X n (nesym HXY),
  fun v n => @vec_change_eq nat _ v X X n erefl,
  fun v n => @vec_change_eq nat _ v Y Y n erefl,
  fun v => @vec_change_same nat _ v X,
  fun v => @vec_change_same nat _ v Y).

Lemma vec_change_same' {X : Type} {n : nat} {v : vec X n} {p : pos n} {x : X} :
  vec_pos v p = x -> vec_change v p x = v.
Proof. move=> <-. by apply: vec_change_same. Qed.

(* compose MMA sub-procedures into one MMA procedure *)
Fixpoint compose (codes : list (nat -> list mm_instr)) (offset : nat) :=
  match codes with
  | nil => []
  | code :: codes => code offset ++ compose codes ((length (code offset))+offset)
  end.

Fact sss_compute_refl i P (st : mm_state) : (i, P) // st ->> st.
Proof.  exists 0. by apply: in_sss_steps_0. Qed.

Fact sss_compute_refl' i P (st1 st2 : mm_state) : st1 = st2 -> (i, P) // st1 ->> st2.
Proof. move=> ->. by apply: sss_compute_refl. Qed.

Lemma subcode_nth_compose i j codes offset :
  j = length (compose (firstn i codes) offset) ->
  subcode.subcode (j + offset, nth i codes (fun=> []) (j + offset)) (offset, compose codes offset).
Proof.
  move=> -> /=.
  elim: codes i offset => /=.
  { rewrite /compose. by move=> [|i] /=; exists nil, nil; rewrite /= Nat.add_0_r. }
  move=> code codes IH [|i] offset /=.
  - eexists nil, _. by rewrite /= Nat.add_0_r.
  - have [l [r [-> Hl]]] := IH i (length (code offset) + offset).
    eexists (code offset ++ l), _. rewrite !app_length. split; [|lia].
    rewrite -!app_assoc. do 3 congr app. congr (nth i codes). lia.
Qed.

(* uses uniform subproc compose structure *)
Lemma compose_sss_compute_trans {codes : list (nat -> list mm_instr)} {offset} (i : nat) {v st st'} :
  let j := length (compose (firstn i codes) offset) in
  (j + offset, (nth i codes (fun _ => [])) (j+offset)) // (j + offset, v) ->> st' ->
  (offset, compose codes offset) // st' ->> st ->
  (offset, compose codes offset) // (j + offset, v) ->> st.
Proof.
  move=> j H. apply: sss_compute_trans.
  move: H. apply: subcode_sss_compute. by apply: subcode_nth_compose.
Qed.

Lemma compose_sss_progress_trans {codes : list (nat -> list mm_instr)} {offset} (i : nat) {v st st'} :
  let j := length (compose (firstn i codes) offset) in
  (j + offset, (nth i codes (fun _ => [])) (j+offset)) // (j + offset, v) -+> st' ->
  (offset, compose codes offset) // st' ->> st ->
  (offset, compose codes offset) // (j + offset, v) -+> st.
Proof.
  move=> j H. apply: sss_progress_compute_trans.
  move: H. apply: subcode_sss_progress. by apply: subcode_nth_compose.
Qed.

Lemma compose_sss_compute_length_trans (i : nat) {codes : list (nat -> list mm_instr)} {lengths} {offset} {v st st'} :
  Forall2 (fun c l => forall j, length (c j) = l) codes lengths ->
  let j := list_sum (firstn i lengths) in
  (j + offset, (nth i codes (fun _ => [])) (j+offset)) // (j + offset, v) ->> st' ->
  (offset, compose codes offset) // st' ->> st ->
  (offset, compose codes offset) // (j + offset, v) ->> st.
Proof.
  move=> Hcl.
  suff -> : list_sum (firstn i lengths) = length (compose (firstn i codes) offset) by apply: compose_sss_compute_trans.
  elim: Hcl i offset. { by case. }
  move=> c l {}codes {}lengths Hcl _ IH [|i] offset. { done. }
  by rewrite /= app_length -IH Hcl.
Qed.

Lemma length_compose {codes lengths offset} :
  Forall2 (fun c l => forall i, length (c i) = l) codes lengths ->
  length (compose codes offset) = list_sum lengths.
Proof.
  move=> H. elim: H offset; [done|].
  move=> c l {}codes {}lengths Hcl _ IH offset.
  by rewrite /= app_length Hcl IH.
Qed.

Arguments compose : simpl never.
Arguments plus : simpl never.

Definition INC X (offset : nat) : list mm_instr := [INC X].

Definition INC_len := 1.

Lemma INC_spec X v offset :
  (offset, INC X offset) // (offset, v) ->>
    (1 + offset, vec_change v X (S (vec_pos v X))).
Proof.
  exists 1. apply: in_sss_steps_S; [|by apply: in_sss_steps_0].
  eexists offset, nil, _, nil, v. rewrite /= Nat.add_0_r.
  by split; [|split;[|constructor]].
Qed.

Definition DEC X p (offset : nat) : list mm_instr := [DEC X p].

Definition DEC_len := 1.

Lemma DEC_spec X p v offset :
  (offset, DEC X p offset) // (offset, v) ->>
    match vec_pos v X with
    | 0 => (1 + offset, v)
    | S x => (p, vec_change v X x)
    end.
Proof.
  exists 1. apply: in_sss_steps_S; [|by apply: in_sss_steps_0].
  eexists offset, nil, _, nil, v. rewrite /= Nat.add_0_r.
  split; [done|split;[done|]].
  case EX: (v#>X) => [|n]; by constructor.
Qed.

(* jump to address p; A is auxiliary *)
Definition JMP_codes (A : counter) (p : nat) (offset : nat) : list (nat -> list mm_instr) :=
  INC A ::
  DEC A p :: [].

Definition JMP A p (offset : nat) := compose (JMP_codes A p offset) offset.

Definition JMP_len := INC_len+DEC_len.

Lemma JMP_spec A p v offset :
  (offset, JMP A p offset) // (offset, v) ->> (p, v).
Proof.
  rewrite /=. apply: (compose_sss_compute_trans 0). { by apply: INC_spec. }
  rewrite /=. apply: (compose_sss_compute_trans 1). { by apply: DEC_spec. }
  rewrite /= (vec_change_eq _ _ erefl) vec_change_idem vec_change_same.
  by apply sss_compute_refl.
Qed.

(* IF X = 0 then GOTO p else continue *)
Definition JZ_codes (X: counter) (p: nat) (offset: nat) : list (nat -> list mm_instr) :=
  DEC X ((DEC_len+JMP_len)+offset) ::
  JMP X p ::
  INC X :: [].

Definition JZ (X: counter) (p: nat) (offset: nat) := compose (JZ_codes X p offset) offset.

Definition JZ_len := DEC_len+JMP_len+INC_len.

Lemma JZ_spec X p v offset :
  (offset, JZ X p offset) // (offset, v) ->> (if vec_pos v X is 0 then p else JZ_len+offset, v).
Proof.
  case EX: (vec_pos v X) => [|n].
  - apply: (compose_sss_compute_trans 0). { by apply: DEC_spec. }
    rewrite EX. apply: (compose_sss_compute_trans 1). { by apply: JMP_spec. }
    by apply: sss_compute_refl.
  - apply: (compose_sss_compute_trans 0). { by apply: DEC_spec. }
    rewrite EX. apply: (compose_sss_compute_trans 2). { by apply: INC_spec. }
    apply: sss_compute_refl'. congr pair.
    by rewrite vec_change_idem vec_change_eq // vec_change_same'.
Qed.

(* X := 0 *)
Definition ZERO_codes (X: counter) (offset: nat) : list (nat -> list mm_instr) :=
  DEC X (offset) :: [].

Definition ZERO (X: counter) (offset: nat) := compose (ZERO_codes X offset) offset.

Definition ZERO_len := DEC_len.

Lemma ZERO_spec X v offset :
  (offset, ZERO X offset) // (offset, v) ->>
  (ZERO_len+offset, vec_change v X 0).
Proof.
  elim /(induction_ltof1 _ (fun w => vec_pos w X)) : v => v IH.
  case EX: (vec_pos v X) => [|n].
  { apply: (compose_sss_compute_trans 0). { by apply: DEC_spec. }
    rewrite EX (vec_change_same' EX).
    by apply: sss_compute_refl. }
  apply: (compose_sss_compute_trans 0). { by apply: DEC_spec. }
  rewrite EX. apply: sss_compute_trans. { apply: IH. by rewrite /= EX vec_change_eq. }
  apply: sss_compute_refl'. by rewrite vec_change_idem.
Qed.

(* Y := X + Y; X := 0 *)
Definition MOVE_codes (X: counter) (Y : counter) (offset: nat) : list (nat -> list mm_instr) :=
    JMP X ((JMP_len + INC_len) + offset) ::
    INC Y ::
    DEC X (JMP_len+offset) :: [].

Definition MOVE (X: counter) (Y : counter) (offset: nat) := compose (MOVE_codes X Y offset) offset.

Definition MOVE_len := JMP_len+INC_len+DEC_len.

Lemma MOVE_spec X Y v offset :
  X <> Y ->
  (offset, MOVE X Y offset) // (offset, v) ->>
  (MOVE_len+offset, vec_change (vec_change v Y (vec_pos v Y + vec_pos v X)) X 0).
Proof.
  move=> HXY.
  apply: (compose_sss_compute_trans 0). { by apply: JMP_spec. }
  elim /(induction_ltof1 _ (fun w => vec_pos w X)) : v => v IH.
  case EX: (vec_pos v X) => [|n].
  { apply: (compose_sss_compute_trans 2). { by apply: DEC_spec. }
    rewrite EX Nat.add_0_r vec_change_same (vec_change_same' EX).
    by apply: sss_compute_refl. }
  apply: (compose_sss_compute_trans 2). { by apply: DEC_spec. }
  rewrite EX. apply: (compose_sss_compute_trans 1). { by apply: INC_spec. }
  apply: sss_compute_trans. { apply: IH. rewrite /= !(vec_norm HXY) EX. lia. }
  apply: sss_compute_refl'. by rewrite !(vec_norm HXY) Nat.add_succ_comm.
Qed.

(* Y := X + Y; Z := X + Z; X := 0 *)
Definition MOVE2_codes (X Y Z: counter) (offset: nat) : list (nat -> list mm_instr) :=
    JMP X ((JMP_len+INC_len+INC_len) + offset) ::
    INC Y ::
    INC Z ::
    DEC X (JMP_len+offset) :: [].

Definition MOVE2 (X Y Z: counter) (offset: nat) := compose (MOVE2_codes X Y Z offset) offset.

Definition MOVE2_len := JMP_len+INC_len+INC_len+DEC_len.

Lemma MOVE2_spec X Y Z v offset :
  X <> Y -> X <> Z ->
  (offset, MOVE2 X Y Z offset) // (offset, v) ->>
  (MOVE2_len+offset, vec_change (vec_change (vec_change v Z (vec_pos v Z + vec_pos v X)) Y (vec_pos ((vec_change v Z (vec_pos v Z + vec_pos v X))) Y + vec_pos v X)) X 0).
Proof.
  move=> HXY HXZ.
  apply: (compose_sss_compute_trans 0). { by apply: JMP_spec. }
  elim /(induction_ltof1 _ (fun w => vec_pos w X)) : v => v IH.
  case EX: (vec_pos v X) => [|n].
  { apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
    rewrite EX !Nat.add_0_r !vec_change_same (vec_change_same' EX).
    by apply: sss_compute_refl. }
  apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
  rewrite EX. apply: (compose_sss_compute_trans 1). { by apply: INC_spec. }
  apply: (compose_sss_compute_trans 2). { by apply: INC_spec. }
  apply: sss_compute_trans. { apply: IH. by rewrite /= !(vec_norm HXY) !(vec_norm HXZ) EX. }
  apply: sss_compute_refl'. congr pair.
  have [<-|HYZ] := pos_eq_dec Y Z.
  - by rewrite !(vec_norm HXY) -!Nat.add_succ_comm.
  - do 2 rewrite ?(vec_norm HXY) ?(vec_norm HXZ) ?(vec_norm HYZ).
    by rewrite -!Nat.add_succ_comm.
Qed.

(* X := (X+X+1)*(2^Y); A := 0; Y := 0
   A is auxiliary *)
Definition PACK_codes (A X Y : counter) (offset: nat) : list (nat -> list mm_instr) :=
  ZERO A :: 
  MOVE2 X A A ::
  INC A ::
  MOVE A X ::
  JMP A ((ZERO_len+MOVE2_len+INC_len+MOVE_len+JMP_len+MOVE2_len+MOVE_len)+offset) ::
  MOVE2 X A A ::
  MOVE A X ::
  DEC Y ((ZERO_len+MOVE2_len+INC_len+MOVE_len+JMP_len)+offset) :: [].

Definition PACK (A X Y : counter) (offset: nat) := compose (PACK_codes A X Y offset) offset.

Definition PACK_len := ZERO_len+MOVE2_len+INC_len+MOVE_len+JMP_len+MOVE2_len+MOVE_len+DEC_len.

Lemma PACK_len_spec A X Y offset : length (PACK A X Y offset) = PACK_len.
Proof. done. Qed. 

Lemma PACK_spec A X Y v offset :
  let x := vec_pos v X in
  let y := vec_pos v Y in
  A <> X -> A <> Y -> X <> Y ->
  (offset, PACK A X Y offset) // (offset, v) ->>
    (PACK_len+offset, vec_change (vec_change (vec_change v X ((x+x+1) * (2 ^ y))) Y 0) A 0).
Proof.
  move=> /= /[dup] HX /nesym H'X /[dup] HY /nesym H'Y HXY.
  apply: (compose_sss_compute_trans 0). { by apply: ZERO_spec. }
  apply: (compose_sss_compute_trans 1). { by apply: MOVE2_spec. }
  apply: (compose_sss_compute_trans 2). { by apply: INC_spec. }
  apply: (compose_sss_compute_trans 3). { by apply: MOVE_spec. }
  apply: (compose_sss_compute_trans 4). { by apply: JMP_spec. }
  rewrite !(vec_norm HX) !Nat.add_0_l.
  have -> : S ((v#>X) + (v#>X)) = (v#>X) + (v#>X) + 1 by lia.
  move: ((v#>X) + (v#>X) + 1).
  elim /(induction_ltof1 _ (fun w => vec_pos w Y)) : v => v IH x.
  case EY: (vec_pos v Y) => [|n].
  { apply: (compose_sss_compute_trans 7). { by apply: DEC_spec. }
    rewrite !(vec_norm HY) !(vec_norm HXY) EY.
    apply: sss_compute_refl'. congr pair.
    by rewrite (vec_change_same' EY) /= Nat.mul_1_r. }
  apply: (compose_sss_compute_trans 7). { by apply: DEC_spec. }
  rewrite !(vec_norm HY) !(vec_norm HXY) EY.
  apply: (compose_sss_compute_trans 5). { by apply: MOVE2_spec. }
  apply: (compose_sss_compute_trans 6). { by apply: MOVE_spec. }
  do 2 rewrite ?(vec_norm HX) ?(vec_norm HY) ?(vec_norm HXY).
  apply: sss_compute_trans. { apply: IH. by rewrite /= !(vec_norm HY) EY. }
  apply: sss_compute_refl'. congr pair.
  rewrite ?(vec_norm HX) ?(vec_norm HY) ?(vec_norm HXY).
  rewrite /=. do 2 congr vec_change. lia.
Qed.

(* X := X/2 if X even goto p else continue *)
Definition HALF_codes (A X: counter) (p: nat) (offset: nat) : list (nat -> list mm_instr) :=
  ZERO A ::
  MOVE X A ::
  JMP A ((ZERO_len+MOVE_len+JMP_len+INC_len)+offset) ::
  INC X ::
  DEC A ((ZERO_len+MOVE_len+JMP_len+INC_len+DEC_len+JMP_len)+offset) ::
  JMP A p ::
  DEC A ((ZERO_len+MOVE_len+JMP_len)+offset) :: [].

Definition HALF (A X : counter) (p: nat) (offset: nat) := compose (HALF_codes A X p offset) offset.

Definition HALF_len := ZERO_len+MOVE_len+JMP_len+INC_len+DEC_len+JMP_len+DEC_len.

(* second component is true iff n is even *)
Fixpoint half (n: nat) : (nat * bool) :=
  match n with
  | 0 => (0, true)
  | S n' => 
      match half n' with
      | (m, b) => if b then (m, false) else (S m, true)
      end
  end.

Lemma half_spec n :
  let '(m, b) := half n in n = (if b then 0 else 1) + m + m.
Proof. elim: n => [|n] /=; [done|case: (half n) => ? []; lia]. Qed.

Lemma half_spec_odd n : half ((n + n + 1) * 2 ^ 0) = (n, false).
Proof.
  have := half_spec ((n + n + 1) * 2 ^ 0).
  case: (half _) => m [] /= *; congr pair; lia.
Qed.

Lemma half_spec_even n m : half ((n + n + 1) * 2 ^ (S m)) = ((n + n + 1) * 2 ^ m, true).
Proof.
  have := half_spec ((n + n + 1) * 2 ^ (S m)).
  case: (half _) => k []; rewrite /= => ?; congr pair; lia.
Qed.

Lemma HALF_spec A X p v offset :
  let x := vec_pos v X in
  A <> X ->
  (offset, HALF A X p offset) // (offset, v) ->>
    let '(m, b) := half x in (if b then p else HALF_len + offset, vec_change (vec_change v X m) A 0).
Proof.
  move=> /= /[dup] HX /nesym  H'X.
  apply: (compose_sss_compute_trans 0). { by apply: ZERO_spec. }
  apply: (compose_sss_compute_trans 1). { by apply: MOVE_spec. }
  apply: (compose_sss_compute_trans 2). { by apply: JMP_spec. }
  rewrite !(vec_norm HX) Nat.add_0_l.
  suff: forall w, (offset, HALF A X p offset) //
    (ZERO_len+MOVE_len+JMP_len+INC_len+offset, w) ->>
    (let '(m, b) := half (vec_pos w A) in (if b then p else HALF_len + offset,
      vec_change (vec_change w X (vec_pos w X+m)) A 0)).
  { move=> H. apply: sss_compute_trans; [apply: H|].
    apply: sss_compute_refl'. rewrite !(vec_norm HX).
    case: (half _) => [? ?]. by rewrite !(vec_norm HX). }
  elim /(induction_ltof1 _ (fun w => vec_pos w A)) => {}v IH.
  case EA: (vec_pos v A) => [|[|n]].
  - apply: (compose_sss_compute_trans 4). { by apply: DEC_spec. }
    rewrite EA. apply: (compose_sss_compute_trans 5). { by apply: JMP_spec. }
    rewrite Nat.add_0_r !(vec_norm HX) (vec_change_same' EA).
    by apply: sss_compute_refl.
  - apply: (compose_sss_compute_trans 4). { by apply: DEC_spec. }
    rewrite EA. apply: (compose_sss_compute_trans 6). { by apply: DEC_spec. }
    rewrite Nat.add_0_r !(vec_norm HX).
    by apply: sss_compute_refl.
  - apply: (compose_sss_compute_trans 4). { by apply: DEC_spec. }
    rewrite EA. apply: (compose_sss_compute_trans 6). { by apply: DEC_spec. }
    rewrite vec_change_eq //. apply: (compose_sss_compute_trans 3). { by apply: INC_spec. }
    apply: sss_compute_trans. { apply: IH. rewrite /= !(vec_norm HX) EA. lia. }
    apply: sss_compute_refl'. rewrite !(vec_norm HX) /=.
    case: (half n) => [m []]; congr pair; by rewrite !(vec_norm HX) Nat.add_succ_comm.
Qed.

(* IF X = (n+n+1)*2^m THEN X := n AND Y := m 
   A is auxiliary *)
Definition UNPACK_codes (A X Y: counter) (offset: nat) : list (nat -> list mm_instr) :=
  JZ X 0 ::
  ZERO Y ::
  JMP A ((JZ_len+ZERO_len+JMP_len+INC_len)+offset) ::
  INC Y ::
  HALF A X ((JZ_len+ZERO_len+JMP_len)+offset) :: [].

Definition UNPACK (A X Y: counter) (offset: nat) := compose (UNPACK_codes A X Y offset) offset.

Definition UNPACK_len := JZ_len+ZERO_len+JMP_len+INC_len+HALF_len.

Lemma UNPACK_spec {A X Y m n v offset} :
  let x := vec_pos v X in
  x = (n + n + 1) * (2 ^ m) ->
  A <> X -> A <> Y -> X <> Y ->
  (offset, UNPACK A X Y offset) // (offset, v) ->>
    (UNPACK_len + offset, vec_change (vec_change (vec_change v X n) Y m) A 0).
Proof.
  move=> /= H'X HX HY HXY.
  apply: (compose_sss_compute_trans 0). { by apply: JZ_spec. }
  have ->: vec_pos v X = S (vec_pos v X - 1).
  { rewrite H'X. have := Nat.pow_nonzero 2 m. lia. }
  apply: (compose_sss_compute_trans 1). { by apply: ZERO_spec. }
  apply: (compose_sss_compute_trans 2). { by apply: JMP_spec. }
  suff: forall w, vec_pos w X = (n + n + 1) * 2 ^ m ->
    (offset, UNPACK A X Y offset) //
    ((JZ_len+ZERO_len+JMP_len+INC_len) + offset, w) ->>
    (UNPACK_len + offset, vec_change (vec_change (vec_change w X n) Y (m+vec_pos w Y)) A 0).
  { move=> H. apply: sss_compute_trans. { apply: H. by rewrite !(vec_norm HXY). }
    apply: sss_compute_refl'. congr pair. by rewrite !(vec_norm HXY) Nat.add_0_r. }
  elim: m {H'X}.
  { move=> w H'X.
    apply: (compose_sss_compute_trans 4). { by apply: HALF_spec. }
    rewrite H'X half_spec_odd Nat.add_0_l !(vec_norm HXY).
    by apply: sss_compute_refl. }
  move=> m IH w H'X.
  apply: (compose_sss_compute_trans 4). { by apply: HALF_spec. }
  rewrite H'X half_spec_even.
  apply: (compose_sss_compute_trans 3). { by apply: INC_spec. }
  apply: sss_compute_trans. { apply: IH. by rewrite !(vec_norm HXY) !(vec_norm HX). }
  apply: sss_compute_refl'. congr pair.
  do ? rewrite ?(vec_norm HXY) ?(vec_norm HX) ?(vec_norm HY).
  by rewrite Nat.add_succ_comm.
Qed.

Lemma UNPACK0_spec {A X Y v offset} :
  vec_pos v X = 0 ->
  (offset, UNPACK A X Y offset) // (offset, v) ->> (0, v).
Proof.
  move=> H'X.
  apply: (compose_sss_compute_trans 0). { by apply: JZ_spec. }
  rewrite H'X. by apply: sss_compute_refl.
Qed.

End FixCounters.
