(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Reduction from:
    Krivine machine halting for closed terms (KrivineMclosed_HALT)
  to:
    Alternate Minsky machine halting (MMA_HALTING)

  Notes:
    This reduction establishes (via wCNB) a link between
    L halting and Minsky machine halting without Turing machine simulation.
    However, complexity information is lost.
*)

From Undecidability Require Import
  MinskyMachines.MM MinskyMachines.MMA LambdaCalculus.Krivine LambdaCalculus.Util.Krivine_facts.
From Undecidability Require
  MinskyMachines.MMA.mma_defs.
From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Require Import PeanoNat List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.

Import L (term, var, app, lam).

Set Default Goal Selector "!".

Module Argument.

#[local] Unset Implicit Arguments.

#[local] Notation mm_instr := (mm_instr (pos 5)).
#[local] Notation counter := (pos 5).
#[local] Notation mm_state := (mm_state 5).

#[local] Notation "P // s ->> t" := (sss_compute (@mma_sss 5) P s t).
#[local] Notation "P // s -+> t" := (sss_progress (@mma_sss 5) P s t).
#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

#[local] Arguments vec_change_neq {X n v p q x}.
#[local] Arguments vec_change_eq {X n v p q x}.
#[local] Arguments vec_change_comm {X n v p q x y}.

Lemma vec_change_same' {X : Type} {n : nat} (v : vec X n) (p : pos n) (x : X) :
  vec_pos v p = x -> vec_change v p x = v.
Proof. move=> <-. by apply: vec_change_same. Qed.

(* auxiliary counters *)
#[local] Notation A := (Fin.F1 : counter).
#[local] Notation B := (Fin.FS (Fin.F1) : counter).
(* data counters *)
#[local] Notation TS := (Fin.FS (Fin.FS (Fin.F1)) : counter).
#[local] Notation CTX := (Fin.FS (Fin.FS (Fin.FS (Fin.F1))) : counter).
#[local] Notation U := (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) : counter).

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

Fact sss_compute_refl i P (st : mm_state) : (i, P) // st ->> st.
Proof. exists 0. by apply: in_sss_steps_0. Qed.

Fact sss_compute_refl' i P (st1 st2 : mm_state) : st1 = st2 -> (i, P) // st1 ->> st2.
Proof. move=> ->. by apply: sss_compute_refl. Qed.

Lemma sss_compute_progress P st st' : P // st ->> st' -> st <> st' -> P // st -+> st'.
Proof.
  move=> [[|k]].
  - by move=> /sss_steps_0_inv.
  - move=> Hk _. exists (S k). by split; [lia|].
Qed.

Lemma mma_step {P : list mm_instr} {offset} i {v st} : 
  match nth_error P i with
  | Some (INC X) =>
      (offset, P) // (1 + i + offset, vec_change v X (S (vec_pos v X))) ->> st
  | Some (DEC X p) =>
      match vec_pos v X with
      | 0 => (offset, P) // (1 + i + offset, v) ->> st
      | S n => (offset, P) // (p, vec_change v X n) ->> st
      end
  | None => False
  end ->
  (offset, P) // (i + offset, v) ->> st.
Proof.
  case EPi: (nth_error P i) => [instr|]; last done.
  move: EPi => /(@nth_error_split mm_instr) => - [l] [r] [-> <-].
  case: instr.
  - move=> ?. apply: sss_compute_trans. exists 1.
    apply: in_sss_steps_S; [|by apply: in_sss_steps_0].
    do 5 eexists. split; [done|]. rewrite (Nat.add_comm offset).
    split; [done|]. by apply: in_mma_sss_inc.
  - move=> X ?. case E: (vec_pos v X) => [|?].
    + apply: sss_compute_trans. exists 1.
      apply: in_sss_steps_S; [|by apply: in_sss_steps_0].
      do 5 eexists. split; [done|]. rewrite (Nat.add_comm offset).
      split; [done|]. by apply: in_mma_sss_dec_0.
    + apply: sss_compute_trans. exists 1.
      apply: in_sss_steps_S; [|by apply: in_sss_steps_0].
      do 5 eexists. split; [done|]. rewrite (Nat.add_comm offset).
      split; [done|]. by apply: in_mma_sss_dec_1.
Qed.

(* uses uniform subproc concat structure *)
Lemma concat_sss_compute_trans {Ps : list (list mm_instr)} {offset} (i : nat) {v st st'} :
  let j := length (concat (firstn i Ps)) in
  (j + offset, nth i Ps []) // (j + offset, v) ->> st' ->
  (offset, concat Ps) // st' ->> st ->
  (offset, concat Ps) // (j + offset, v) ->> st.
Proof.
  move=> j H. apply: sss_compute_trans.
  have : ({(j + offset, v) = st'} + {(j + offset, v) <> st'}).
  { do ? decide equality. apply: vec_eq_dec. by apply: Nat.eq_dec. }
  move=> [<-|H']. { by apply: sss_compute_refl. }
  apply: (subcode_sss_compute (P := (_, nth i Ps []))).
  - exists (concat (firstn i Ps)), (concat (skipn (S i) Ps)).
    split; last done.
    have -> : nth i Ps [] = concat [nth i Ps []].
    { by rewrite /concat app_nil_r. }
    rewrite -?concat_app. congr concat.
    rewrite [LHS](esym (firstn_skipn i Ps)). congr List.app.
    have : nth i Ps [] <> [].
    { move=> H''. move: H. rewrite H''.
      move=> [[|k]].
      - by move=> /sss_steps_0_inv.
      - move=> /sss_steps_S_inv' [?] [+ _].
        by move=> [?] [[|??]] [?] [?] [?] [[]]. }
    elim: (i) (Ps); first by case.
    move=> i' IH [|? ?]; first done.
    rewrite !skipn_cons. by apply: IH.
  - by rewrite (Nat.add_comm offset).
Qed.

#[local] Arguments plus : simpl never.
#[local] Arguments concat : simpl never.

(* jump to address p *)
Definition JMP p : list mm_instr :=
  [INC A; DEC A p].

Definition JMP_len := length (JMP 0).

Lemma JMP_spec p v offset :
  (offset, JMP p) // (0 + offset, v) ->> (p, v).
Proof.
  apply: mma_step. apply: mma_step.
  rewrite /= (vec_change_eq erefl) vec_change_idem vec_change_same.
  by apply: sss_compute_refl.
Qed.

(* foreach Y in Ys : Y := Y + X; X := 0 *)
Definition MOVE (X: counter) (Ys : list counter) (offset: nat) : list mm_instr :=
  concat (
    JMP (JMP_len + length Ys + offset) ::
    map (@INC _) Ys ::
    [DEC X (2+offset)] :: []).

Definition MOVE_len n := JMP_len + n + 1.

Lemma MOVE_spec X Ys v offset :
  let x := vec_pos v X in
  match Ys with
  | [] => True
  | [Y] => X <> Y
  | [Y1; Y2] => X <> Y1 /\ X <> Y2
  | _ => False
  end ->
  (offset, MOVE X Ys offset) // (offset, v) ->> ((MOVE_len (length Ys))+offset,
    vec_change (fold_right (fun Y w => vec_change w Y (vec_pos w Y + x)) v Ys) X 0).
Proof.
  move=> /= HXYs.
  apply: (concat_sss_compute_trans 0). { by apply: JMP_spec. }
  move En: (vec_pos v X) => n.
  move Ew: (vec_change _ X 0) => w.
  elim: n v En w Ew.
  - move=> v En w <-.
    apply: mma_step. rewrite /= nth_error_app2 map_length. { done. }
    rewrite Nat.sub_diag /= En.
    apply: sss_compute_refl'. congr pair. { rewrite /MOVE_len. lia. }
    move: Ys HXYs => [|Y1 [|Y2 [|Y3 ?]]] /= *.
    all: rewrite !vec_change_same'; by [|lia].
  - move=> n IH v En w <-.
    apply: mma_step. rewrite /= nth_error_app2 map_length. { done. }
    rewrite Nat.sub_diag /= En.
    move: Ys HXYs IH => [|Y1 [|Y2 [|Y3 ?]]] /= HXYs IH; last done.
    + apply: IH.
      * by rewrite vec_change_eq.
      * by rewrite vec_change_idem.
    + apply: mma_step.
      apply: IH. { by rewrite !(vec_norm HXYs). }
      rewrite !(vec_norm HXYs). do ? congr vec_change. lia.
    + apply: mma_step. apply: mma_step.
      have [HXY1 HXY2] := HXYs.
      apply: IH. { by rewrite !(vec_norm HXY1) !(vec_norm HXY2). }
      have [<-|HY1Y2] := pos_eq_dec Y1 Y2.
      * rewrite !(vec_norm HXY1). do ? congr vec_change. lia.
      * do 2 rewrite ?(vec_norm HXY1) ?(vec_norm HXY2) ?(vec_norm HY1Y2).
        do ? congr vec_change; lia.
Qed.

(* X := 0 *)
Definition ZERO (X: counter) (offset: nat) : list mm_instr :=
  MOVE X [] offset.

Definition ZERO_len := MOVE_len 0.

Lemma ZERO_spec X v offset :
  (offset, ZERO X offset) // (0 + offset, v) ->> (ZERO_len+offset, vec_change v X 0).
Proof. by apply: MOVE_spec. Qed.

(* X := X+X *)
Definition DOUBLE (X: counter) (offset: nat) : list mm_instr :=
  concat (
    let i := offset in ZERO A offset ::
    let i := ZERO_len + i in MOVE X [A;A] i :: 
    let i := MOVE_len 2 + i in MOVE A [X] i :: 
    []).

Definition DOUBLE_len := length (DOUBLE A 0).

Lemma DOUBLE_spec X v offset :
  let x := vec_pos v X in
  A <> X ->
  (offset, DOUBLE X offset) // (offset, v) ->>
    (DOUBLE_len+offset, vec_change (vec_change v X (x+x)) A 0).
Proof.
  move=> /= /[dup] HX /nesym H'X.
  apply: (concat_sss_compute_trans 0). { by apply: ZERO_spec. }
  apply: (concat_sss_compute_trans 1). { by apply: MOVE_spec. }
  apply: (concat_sss_compute_trans 2). { by apply: MOVE_spec. }
  apply: sss_compute_refl'. by rewrite /= !(vec_norm HX).
Qed.

(* X := (X+X+1)*(2^Y) *)
Definition PACK (X Y: counter) (offset: nat) : list mm_instr :=
  concat (
    DOUBLE X offset ::
    let i := DOUBLE_len + offset in [INC X] ::
    let i := 1 + i in JMP (DOUBLE_len+JMP_len+i) ::
    let i := JMP_len + i in DOUBLE X i ::
    [DEC Y i] :: []).

Definition PACK_len := length (PACK A A 0).

Lemma PACK_spec X Y v offset :
  let x := vec_pos v X in
  let y := vec_pos v Y in
  A <> X -> A <> Y -> X <> Y ->
  (offset, PACK X Y offset) // (offset, v) ->>
    (PACK_len+offset, vec_change (vec_change (vec_change v X ((x+x+1) * (2 ^ y))) Y 0) A 0).
Proof.
  move=> /= HX HY HXY.
  apply: (concat_sss_compute_trans 0). { by apply: DOUBLE_spec. }
  apply: mma_step.
  apply: (concat_sss_compute_trans 2). { by apply: JMP_spec. }
  move Ev': (v' in _ // (_, v') ->> _) => v'.
  have HAv' : vec_pos v' A = 0.
  { by rewrite -Ev' (vec_change_neq (nesym HX)) vec_change_eq. }
  have :
    let x := vec_pos v' X in let y := vec_pos v' Y in
    forall w, w = vec_change (vec_change (vec_change v' A 0) Y 0) X (x * (2 ^ y)) ->
    (offset, PACK X Y offset) //
    (DOUBLE_len + JMP_len + (1 + (DOUBLE_len + offset)), v') ->>
    (1 + DOUBLE_len + JMP_len + (1 + (DOUBLE_len + offset)), w).
  { move En: (vec_pos v' Y) => n /=.
    elim: n (v') En HAv'.
    - move=> v'' En HAv'' w ->.
      rewrite ?(Nat.add_assoc _ _ offset). apply: mma_step. rewrite /= En.
      apply: sss_compute_refl'. congr pair.
      rewrite (vec_change_same' _ A) // (vec_change_same' _ Y) // vec_change_same' //=.
      lia.
    - move=> n IH v'' En HAv'' w ->.
      rewrite ?(Nat.add_assoc _ _ offset). apply: mma_step. rewrite /= En.
      apply: (concat_sss_compute_trans 3). { by apply: DOUBLE_spec. }
      apply: IH.
      + by rewrite !(vec_change_neq HY) !(vec_change_neq HXY) vec_change_eq.
      + by rewrite vec_change_eq.
      + rewrite !(vec_norm HY) !(vec_norm HX) !(vec_norm HXY) /=.
        congr vec_change. congr vec_change. lia. }
  move=> /(_ _ erefl) /sss_compute_trans. apply.
  apply: sss_compute_refl'. congr pair.
  rewrite -Ev' /=. do ? rewrite ?(vec_norm HY) ?(vec_norm HX) ?(vec_norm HXY).
  congr vec_change. congr vec_change. lia.
Qed.

(* X := X/2 + A if X even goto p else continue *)
Definition HALF (X: counter) (p: nat) (offset: nat) : list mm_instr :=
  concat (
    let i := offset in JMP (JMP_len + 1 + i) ::
    let i := JMP_len + i in let j := i in [INC A; DEC X (2+JMP_len+MOVE_len 1+i)] ::
    let i := 2 + i in MOVE A [X] i ::
    let i := MOVE_len 1 + i in JMP p ::
    let i := JMP_len + i in [DEC X j] ::
    let i := 1 + i in MOVE A [X] i :: []).

Definition HALF_len := length (HALF A 0 0).

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

Lemma HALF_spec X p v offset :
  let x := vec_pos v X in let a := vec_pos v A in
  A <> X ->
  (offset, HALF X p offset) // (offset, v) ->>
    let '(m, b) := half x in (if b then p else HALF_len + offset, vec_change (vec_change v X (a+m)) A 0).
Proof.
  move=> /= HX.
  apply: (concat_sss_compute_trans 0). { by apply: JMP_spec. }
  move Hst: (st in _ // _ ->> st) => st.
  elim /(Nat.measure_induction _ (fun v => vec_pos v X)) : v st Hst.
  move=> v IH st <-.
  case EX: (vec_pos v X) => [|[|n]].
  { apply: mma_step. rewrite /= EX.
    apply: (concat_sss_compute_trans 2). { by apply: MOVE_spec. }
    apply: (concat_sss_compute_trans 3). { by apply: JMP_spec. }
    apply: sss_compute_refl'. by rewrite /= EX !Nat.add_0_r. }
  { apply: mma_step. rewrite /= EX ?(Nat.add_assoc _ _ offset).
    apply: mma_step. rewrite /= (vec_change_eq erefl).
    apply: (concat_sss_compute_trans 5). { by apply: MOVE_spec. }
    apply: sss_compute_refl'. by rewrite /= !(vec_norm HX) !Nat.add_0_r. }
  apply: mma_step. rewrite /= EX ?(Nat.add_assoc _ _ offset).
  apply: mma_step. rewrite /= (vec_change_eq erefl).
  apply: mma_step. apply: IH. { rewrite !(vec_norm HX). lia. }
  rewrite !(vec_norm HX) /=.
  have := half_spec n. case: (half n) => m [] ->.
  - rewrite !(vec_norm HX). congr pair. do ? congr vec_change. lia.
  - rewrite !(vec_norm HX). congr pair. do ? congr vec_change. lia.
Qed.

(* IF X = 0 then GOTO p else continue *)
Definition JZ (X: counter) (p: nat) (offset: nat) : list mm_instr :=
  concat (
    let i := offset in [DEC X (JMP_len + 1 + i)] ::
    let i := 1 + i in JMP p ::
    let i := JMP_len + i in [INC X] :: []).

Definition JZ_len := length (JZ A 0 0).

Lemma JZ_spec X p v offset :
  let x := vec_pos v X in
  (offset, JZ X p offset) // (offset, v) ->> (if x is 0 then p else JZ_len+offset, v).
Proof.
  move=> /=.
  case EX: (vec_pos v X) => [|n].
  - apply: (mma_step 0). rewrite /= EX.
    apply: (concat_sss_compute_trans 1). { by apply: JMP_spec. }
    by apply: sss_compute_refl.
  - apply: (mma_step 0). rewrite /= EX. apply: mma_step.
    apply: sss_compute_refl'.
    by rewrite (vec_change_eq erefl) vec_change_idem -EX vec_change_same.
Qed.

(* IF X = (n+n+1)*2^m THEN X := n AND Y := m *)
Definition UNPACK (X Y: counter) (offset: nat) : list mm_instr :=
  concat (
    let i := offset in JZ X 0 i ::
    let i := JZ_len + i in ZERO A i ::
    let i := ZERO_len + i in ZERO Y i ::
    let i := ZERO_len + i in JMP (JMP_len + 1 + i) ::
    let j := JMP_len + i in [INC Y] ::
    let i := 1 + j in HALF X j i :: []).

Definition UNPACK_len := length (UNPACK A A 0).

Lemma UNPACK_spec {X Y m n v offset} :
  let x := vec_pos v X in
  x = (n + n + 1) * (2 ^ m) ->
  A <> X -> A <> Y -> X <> Y ->
  (offset, UNPACK X Y offset) // (offset, v) ->>
    (UNPACK_len + offset, vec_change (vec_change (vec_change v X n) Y m) A 0).
Proof.
  move=> /= H'X HX HY HXY.
  apply: (concat_sss_compute_trans 0). { by apply: JZ_spec. }
  have ->: vec_pos v X = S (vec_pos v X - 1).
  { rewrite H'X. have := Nat.pow_nonzero 2 m. lia. }
  apply: (concat_sss_compute_trans 1). { by apply: ZERO_spec. }
  apply: (concat_sss_compute_trans 2). { by apply: ZERO_spec. }
  apply: (concat_sss_compute_trans 3). { by apply: JMP_spec. }
  suff : forall v' w', 
    w' = vec_change (vec_change v' X n) Y (m + vec_pos v' Y) ->
    vec_pos v' X = (n + n + 1) * 2 ^ m ->
    vec_pos v' A = 0 ->
    (offset, UNPACK X Y offset) //
    (1 + JZ_len + ZERO_len + ZERO_len + JMP_len + offset, v') ->> (UNPACK_len + offset, w').
  { apply.
    - by rewrite !(vec_norm HXY) !(vec_norm HY) !(vec_norm HX) Nat.add_0_r.
    - by rewrite !(vec_norm HXY) !(vec_norm HX).
    - by rewrite !(vec_norm HY). }
  elim: m {H'X}.
  { move=> v' w' -> H'v' H''v'.
    apply: (concat_sss_compute_trans 5). { by apply: HALF_spec. }
    rewrite H'v' half_spec_odd.
    apply: sss_compute_refl'. congr pair.
    rewrite H''v' !Nat.add_0_l !(vec_norm HXY) !(vec_norm (nesym HX)).
    congr vec_change. by rewrite vec_change_same'. }
  move=> m IH v' w' -> H'v' H''v'.
  apply: (concat_sss_compute_trans 5). { by apply: HALF_spec. }
  rewrite H'v' half_spec_even ?(Nat.add_assoc _ _ offset). apply: mma_step.
  apply: IH.
  - do ? rewrite ?(vec_norm (nesym HY)) ?(vec_norm (nesym HX)) ?(vec_norm HXY).
    rewrite (vec_change_same' v' A 0 H''v').
    congr vec_change. congr vec_change. lia.
  - by rewrite !(vec_norm HXY) !(vec_norm HX) H''v'.
  - by rewrite !(vec_norm HY).
Qed.

Lemma UNPACK_spec' {X Y v offset} :
  vec_pos v X = 0 ->
  (offset, UNPACK X Y offset) // (offset, v) ->> (0, v).
Proof.
  move=> H'X.
  apply: (concat_sss_compute_trans 0). { by apply: JZ_spec. }
  rewrite H'X. by apply: sss_compute_refl.
Qed.

Definition enc_pair (m n: nat) := (n+n+1)*(2^m).

Fixpoint enc_term (s: term) : nat :=
  match s with
  | var n => enc_pair 0 n
  | lam s => enc_pair 1 (enc_term s)
  | app s t => enc_pair (2 + enc_term t) (enc_term s)
  end.

Fixpoint enc_list (ns : list nat) : nat :=
  match ns with
  | [] => 0
  | n::ns => enc_pair n (enc_list ns)
  end.

Fixpoint enc_closure (u: eterm) :=
  match u with
  | closure ctx s => enc_pair (enc_list (map enc_closure ctx)) (enc_term s)
  end.

Definition enc_cs ctx := enc_list (map enc_closure ctx).
Arguments enc_cs !ctx /.

Lemma counters_eta (v : vec nat 5) :
  v = Vector.hd v ## 
    Vector.hd (Vector.tl v) ## 
    Vector.hd (Vector.tl (Vector.tl v)) ## 
    Vector.hd (Vector.tl (Vector.tl (Vector.tl v))) ##
    Vector.hd (Vector.tl (Vector.tl (Vector.tl (Vector.tl v)))) ##
    Vector.nil _.
Proof.
  do 5 (rewrite [LHS](Vector.eta v); congr Vector.cons; move: (Vector.tl v) => {}v).
  by apply: vec_0_nil.
Qed.

Definition CASE_VAR0 (p: nat) (offset : nat) : list mm_instr :=
  concat (
    let i := offset in UNPACK CTX U i ::
    let i := UNPACK_len + i in UNPACK U CTX i ::
    let i := UNPACK_len + i in JMP p :: []).

Definition CASE_VAR0_len := length (CASE_VAR0 0 0).

Lemma CASE_VAR0_spec ctx' t' ctx p v offset :
  vec_pos v CTX = enc_cs ((closure ctx' t') :: ctx) ->
  (offset, CASE_VAR0 p offset) // (offset, v) ->>
    (p, vec_change (vec_change (vec_change v U (enc_term t')) CTX (enc_cs ctx')) A 0).
Proof.
  rewrite (counters_eta v) /= => ->.
  apply: (concat_sss_compute_trans 0). { by apply: UNPACK_spec. }
  apply: (concat_sss_compute_trans 1). { by apply: UNPACK_spec. }
  apply: (concat_sss_compute_trans 2). { by apply: JMP_spec. }
  by apply: sss_compute_refl'.
Qed.

Definition CASE_VARS (p: nat) (offset : nat) : list mm_instr :=
  concat (
    let i := offset in UNPACK CTX B i ::
    let i := UNPACK_len + i in ZERO B i ::
    let i := ZERO_len + i in PACK U B i ::
    let i := PACK_len + i in JMP p :: []).

Definition CASE_VARS_len := length (CASE_VARS 0 0).

Lemma CASE_VARS_spec u ctx n p v offset :
  vec_pos v CTX = enc_cs (u :: ctx) ->
  vec_pos v U = n ->
  vec_pos v B = 0 ->
  (offset, CASE_VARS p offset) // (offset, v) ->>
    (p, vec_change (vec_change (vec_change v U (enc_term (var n))) CTX (enc_cs ctx)) A 0).
Proof.
  rewrite (counters_eta v) /= => -> -> ->.
  apply: (concat_sss_compute_trans 0). { by apply: UNPACK_spec. }
  apply: (concat_sss_compute_trans 1). { by apply: ZERO_spec. }
  apply: (concat_sss_compute_trans 2). { by apply: PACK_spec. }
  apply: (concat_sss_compute_trans 3). { by apply: JMP_spec. }
  by apply: sss_compute_refl'.
Qed.

Definition CASE_APP (p: nat) (offset : nat) : list mm_instr :=
  concat (
    let i := offset in PACK B CTX i ::
    let i := PACK_len + i in MOVE B [CTX; A] i ::
    let i := MOVE_len 2 + i in MOVE A [B] i ::
    let i := MOVE_len 1 + i in PACK TS CTX i ::
    let i := PACK_len + i in UNPACK B CTX i ::
    let i := UNPACK_len + i in ZERO B i ::
    let i := ZERO_len + i in JMP p :: []).

Definition CASE_APP_len := length (CASE_APP 0 0).

#[local] Arguments Nat.pow : simpl never.

Lemma CASE_APP_spec ts ctx t p v offset :
  vec_pos v TS = enc_cs ts ->
  vec_pos v CTX = enc_cs ctx ->
  vec_pos v B = enc_term t ->
  (offset, CASE_APP p offset) // (offset, v) ->>
    (p, vec_change (vec_change (vec_change v TS (enc_cs ((closure ctx t)::ts))) B 0) A 0).
Proof.
  rewrite (counters_eta v) /= => -> -> ->.
  rewrite /=. apply: (concat_sss_compute_trans 0). { by apply: PACK_spec. }
  rewrite /=. apply: (concat_sss_compute_trans 1). { by apply: MOVE_spec. }
  rewrite /=. apply: (concat_sss_compute_trans 2). { by apply: MOVE_spec. }
  rewrite /=. apply: (concat_sss_compute_trans 3). { by apply: PACK_spec. }
  rewrite /=. apply: (concat_sss_compute_trans 4). { by apply: UNPACK_spec. }
  rewrite /=. apply: (concat_sss_compute_trans 5). { by apply: ZERO_spec. }
  apply: (concat_sss_compute_trans 6). { by apply: JMP_spec. }
  by apply: sss_compute_refl.
Qed.

Definition CASE_LAM (p: nat) (offset : nat) : list mm_instr :=
  concat (
    let i := offset in UNPACK TS B i ::
    let i := UNPACK_len + i in PACK CTX B i ::
    let i := PACK_len + i in JMP p :: []).

Definition CASE_LAM_len := length (CASE_LAM 0 0).

Lemma CASE_LAM_spec t ts ctx p v offset :
  vec_pos v TS = enc_cs (t :: ts) ->
  vec_pos v CTX = enc_cs ctx ->
  vec_pos v B = 0 ->
  (offset, CASE_LAM p offset) // (offset, v) ->>
    (p, vec_change (vec_change (vec_change v TS (enc_cs ts)) CTX (enc_cs (t::ctx))) A 0).
Proof.
  rewrite (counters_eta v) /= => -> -> ->.
  apply: (concat_sss_compute_trans 0). { by apply: UNPACK_spec. }
  apply: (concat_sss_compute_trans 1). { by apply: PACK_spec. }
  apply: (concat_sss_compute_trans 2). { by apply: JMP_spec. }
  by apply: sss_compute_refl.
Qed.

Lemma CASE_LAM_spec' p v offset :
  vec_pos v TS = enc_cs [] ->
  (offset, CASE_LAM p offset) // (offset, v) ->> (0, v).
Proof.
  rewrite (counters_eta v) /= => ->.
  apply: (concat_sss_compute_trans 0). { by apply: UNPACK_spec'. }
  by apply: sss_compute_refl.
Qed.

(* main simulation routine; by case analysis on current term *)
Definition PROG (offset : nat) : list mm_instr :=
  concat (
    let i := offset in JMP (JMP_len + i) ::
    let i := JMP_len + i in UNPACK U B i ::
    let i := UNPACK_len + i in [DEC B (CASE_VARS_len+CASE_VAR0_len+2+i)] ::
    (* var _ CASE *) let i := 1 + i in [DEC U (CASE_VAR0_len+1+i)] ::
    (* var 0 CASE *) let i := 1 + i in CASE_VAR0 offset i ::
    (* var (S n) CASE *) let i := CASE_VAR0_len + i in CASE_VARS offset i ::
    let i := CASE_VARS_len + i in [DEC B (CASE_LAM_len+1+i)] ::
    (* lam s CASE *) let i := 1 + i in CASE_LAM offset i ::
    (* app s t CASE *) let i := CASE_LAM_len + i in CASE_APP offset i :: []).

Lemma PROG_start_spec offset v w : 
  (offset, PROG offset) //
  (JMP_len + offset, v) ->> (offset, w) ->
  (offset, PROG offset) // (offset, v) -+> (offset, w).
Proof.
  move=> ?.
  apply: sss_progress_compute_trans.
  { apply: sss_compute_progress.
    { by apply: (concat_sss_compute_trans 0); [apply JMP_spec | apply: sss_compute_refl]. }
    case. rewrite /JMP_len /=. lia. }
  done.
Qed.

Lemma PROG_VAR0_spec offset ts ctx ctx' t' :
  (offset, PROG offset) //
  (offset, 0 ## 0 ## enc_cs ts ## enc_cs (closure ctx t' :: ctx') ## enc_term (var 0) ## vec_nil) -+>
  (offset, 0 ## 0 ## enc_cs ts ## enc_cs ctx ## enc_term t' ## vec_nil).
Proof.
  apply: PROG_start_spec.
  apply: (concat_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite /= ?(Nat.add_assoc _ _ offset). apply: mma_step. apply: mma_step.
  apply: (concat_sss_compute_trans 4). { by apply: CASE_VAR0_spec. }
  by apply: sss_compute_refl.
Qed.

Lemma PROG_VARS_spec offset ts ctx n u :
  (offset, PROG offset) //
  (offset, 0 ## 0 ## enc_cs ts ## enc_cs (u :: ctx) ## enc_term (var (S n)) ## vec_nil) -+>
  (offset, 0 ## 0 ## enc_cs ts ## enc_cs ctx ## enc_term (var n) ## vec_nil).
Proof.
  apply: PROG_start_spec.
  apply: (concat_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite /= ?(Nat.add_assoc _ _ offset). apply: mma_step. apply: mma_step.
  apply: (concat_sss_compute_trans 5). { by apply: CASE_VARS_spec. }
  by apply: sss_compute_refl.
Qed.

Lemma PROG_APP_spec offset ts ctx s t :
  (offset, PROG offset) //
  (offset, 0 ## 0 ## enc_cs ts ## enc_cs ctx ## enc_term (app s t) ## vec_nil) -+>
  (offset, 0 ## 0 ## enc_cs (closure ctx t :: ts) ## enc_cs ctx ## enc_term s ## vec_nil).
Proof.
  apply: PROG_start_spec.
  apply: (concat_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite /= ?(Nat.add_assoc _ _ offset). apply: mma_step. apply: mma_step.
  apply: (concat_sss_compute_trans 8). { by apply: CASE_APP_spec. }
  by apply: sss_compute_refl.
Qed.

Lemma PROG_LAM_spec offset t ts ctx s :
  (offset, PROG offset) //
  (offset, 0 ## 0 ## enc_cs (t :: ts) ## enc_cs ctx ## enc_term (lam s) ## vec_nil) -+>
  (offset, 0 ## 0 ## enc_cs ts ## enc_cs (t :: ctx) ## enc_term s ## vec_nil).
Proof.
  apply: PROG_start_spec.
  apply: (concat_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite /= ?(Nat.add_assoc _ _ offset). apply: mma_step. apply: mma_step.
  apply: (concat_sss_compute_trans 7). { by apply: CASE_LAM_spec. }
  by apply: sss_compute_refl.
Qed.

Lemma sss_terminates_sss_compute P x y :
  P // x ->> y ->
  sss_terminates (mma_sss (n:=5)) P y ->
  sss_terminates (mma_sss (n:=5)) P x.
Proof.
  move=> H [z [Hz ?]]. exists z. split; [|done].
  apply: sss_compute_trans; eassumption.
Qed.

Lemma simulation {offset ts ctx t} : 0 < offset -> halt_cbn ts ctx t ->
  let v := (0 ## 0 ## (enc_cs ts) ## (enc_cs ctx) ## (enc_term t) ## Vector.nil _) in
  (sss_terminates (@mma_sss _) (offset, PROG offset) (offset, v)).
Proof.
  move=> ? H. elim: H; clear ts ctx t.
  - move=> > _ /=. apply: sss_terminates_sss_compute.
    apply: sss_progress_compute. by apply: PROG_VAR0_spec.
  - move=> > _ /=. apply: sss_terminates_sss_compute.
    apply: sss_progress_compute. by apply: PROG_VARS_spec.
  - move=> > _ /=. apply: sss_terminates_sss_compute.
    apply: sss_progress_compute. by apply: PROG_APP_spec.
  - move=> > _ /=. apply: sss_terminates_sss_compute.
    apply: sss_progress_compute. by apply: PROG_LAM_spec.
  - move=> /= >. eexists. split.
    + apply: (concat_sss_compute_trans 0). { by apply: JMP_spec. }
      apply: (concat_sss_compute_trans 1). { by apply: UNPACK_spec. }
      rewrite /= ?(Nat.add_assoc _ _ offset). apply: mma_step. apply: mma_step.
      apply: (concat_sss_compute_trans 7). { by apply: CASE_LAM_spec'. }
      by apply: sss_compute_refl.
    + by left.
Qed.

#[local] Notation all := (fold_right and True).

Lemma boundS m n : L_facts.bound (S m) (var (S n)) -> L_facts.bound m (var n).
Proof. move=> /term_facts.boundE ?. constructor. lia. Qed.

Lemma inverse_simulation ts ctx t :
  let v := (0 ## 0 ## (enc_cs ts) ## (enc_cs ctx) ## (enc_term t) ## Vector.nil _) in
  all (map eclosed ts) ->
  eclosed (closure ctx t) ->
  (sss_terminates (@mma_sss _) (1, PROG 1) (1, v)) ->
  halt_cbn ts ctx t.
Proof.
  move=> v. move Ex: (1, v) => x ++ H. subst v.
  move: x H ts ctx t Ex.
  apply: sss_terminates_ind; [ exact: mma_defs.mma_sss_fun | |].
  { move=> [? ?] /= ? > []. lia. }
  move=> [i' v'] IH ts ctx t [? ?].
  move => /(_ _ _ (subcode.subcode_refl (1, PROG 1)) _ _ _ _ erefl) in IH.
  subst i' v'. case: t IH.
  - (* case (var n) *) case.
    + case: ctx => [|[ctx' t'] ctx''].
      { move=> IH _ /= [/term_facts.boundE]. lia. }
      move=> IH ? /= [?] [? ?]. constructor. apply: IH; [|done|done].
      by apply: PROG_VAR0_spec.
    + move=> n. case: ctx => [|[ctx' t'] ctx''].
      { move=> IH _ /= [/term_facts.boundE]. lia. }
      move=> IH ? /= [/boundS ?] [? ?]. constructor. apply: IH; [|done|done].
      by apply: PROG_VARS_spec.
  - (* case app s t *)
    move=> s t IH /= ? [/term_facts.boundE [? ?] ?]. constructor. apply: IH; [|done|done].
    by apply: PROG_APP_spec.
  - move=> s. case: ts => [|t' ts'].
    { move=> *. by constructor. }
    move=> IH /= [? ?] [/term_facts.boundE ? ?]. constructor. apply: IH; [|done|done].
    by apply: PROG_LAM_spec.
Qed.

Definition input t :=
  0 ## 0 ## 0 ## 0 ## enc_term t ## (Vector.nil _).

End Argument.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : KrivineMclosed_HALT ⪯ (@MMA_HALTING 5).
Proof.
  exists (fun '(exist _ t _) => (Argument.PROG 1, Argument.input t)).
  move=> [t /= /eclosed_closed Ht]. split.
  - move=> /Argument.simulation. by apply.
  - move=> /(Argument.inverse_simulation nil nil). by apply.
Qed.
