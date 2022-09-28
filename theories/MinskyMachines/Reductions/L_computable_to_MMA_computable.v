(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  If a relation R is L_computable then it is MMA_computable.

  Idea: simulate wCBV abstract machine by MMA, and inspect resulting closure.
*)

From Undecidability Require Import
  MinskyMachines.MM MinskyMachines.MMA L.L.
From Undecidability Require
  MinskyMachines.MMA.mma_defs L.Util.L_facts.
From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss Code.subcode.

From Undecidability Require Import
  MinskyMachines.Util.MMA_pairing L.AbstractMachines.wCBV.

Require Import PeanoNat List Lia Wf_nat.
Import ListNotations.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

#[local] Unset Implicit Arguments.
#[local] Arguments ltof /.

(* local facts *)
Module Facts.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

Lemma firstn_repeat {X : Type} n {x : X} m : firstn n (repeat x m) = repeat x (Nat.min n m).
Proof.
  elim: n m => [|n IH]. { done. }
  move=> [|m]; [done|].
  by rewrite /= IH.
Qed.

Lemma Forall2_firstn {X Y : Type} {P : X -> Y -> Prop} {l1 l2 n} :
  Forall2 P l1 l2 -> Forall2 P (firstn n l1) (firstn n l2).
Proof.
  move=> H.  elim: H n. { by case=> [|?]; constructor. }
  move=> > ??? [|?]; by constructor.
Qed.

Lemma Forall2_repeat {X Y : Type} {P : X -> Y -> Prop} {l y n} :
  length l = n -> Forall (fun x => P x y) l -> Forall2 P l (repeat y n).
Proof.
  move=> + H. elim: H n.
  - by move=> [|n] ?; [constructor|].
  - move=> > ?? IH [|n]; [done|].
    move=> [/IH] ?. by constructor.
Qed.

Lemma list_sum_repeat n m : list_sum (repeat n m) = m * n.
Proof.
  elim: m. { done. }
  by move=> ? /= ->.
Qed.

Lemma R_inj n m (X Y : Fin.t m) : Fin.R n X = Fin.R n Y -> X = Y.
Proof.
  elim: n. { done. }
  by move=> n IH /= /pos_nxt_inj /IH.
Qed.

Lemma Fin_L_R_neq n m (p : Fin.t n) (q : Fin.t m) : 
  Fin.L m p <> Fin.R n q.
Proof.
  elim: n p m q.
  - by apply: Fin.case0.
  - move=> n IH /= p. move: n p IH. apply: Fin.caseS; [done|].
    move=> > IH > /= /pos_nxt_inj. by apply: IH.
Qed.

Lemma vec_pos_append_R {T : Type} {n} {w : Vector.t T n} {m} {v : Vector.t T m} {X} :
  vec_pos (Vector.append w v) (Fin.R n X) = vec_pos v X.
Proof.
  by elim: w.
Qed.

Lemma vec_change_append_R {T : Type} {n} {w : Vector.t T n} {m} {v : Vector.t T m} {X} {x} :
  vec_change (Vector.append w v) (Fin.R n X) x = Vector.append w (vec_change v X x).
Proof.
  elim: w.
  - done.
  - by move=> > /= ->.
Qed.

Lemma vec_pos_append_L {T : Type} {n} {w : Vector.t T n} {m} {v : Vector.t T m} {X} :
  vec_pos (Vector.append w v) (Fin.L m X) = vec_pos w X.
Proof.
  elim: X w.
  - move=> ? w. by rewrite (Vector.eta w).
  - move=> > IH /= w. by rewrite (Vector.eta w) /=.
Qed.

Lemma vec_change_append_L {T : Type} {n} {w : Vector.t T n} {m} {v : Vector.t T m} {X} {x} :
  vec_change (Vector.append w v) (Fin.L m X) x = Vector.append (vec_change w X x) v.
Proof.
  elim: X w.
  - move=> ? w. by rewrite (Vector.eta w).
  - move=> > IH /= w. by rewrite (Vector.eta w) /= IH.
Qed.

Lemma vec_pos_cons {T : Type} {n} {w : Vector.t T n} x X :
  vec_pos (x ## w) (Fin.FS X) = vec_pos w X.
Proof. done. Qed.

Lemma vec_pos_hd {T : Type} {n} {w : Vector.t T n} x :
  vec_pos (x ## w) (Fin.F1) = x.
Proof. done. Qed.

Lemma vec_change_cons {T : Type} {n} {w : Vector.t T n} x X y :
  vec_change (x ## w) (Fin.FS X) y = x ## vec_change w X y.
Proof. done. Qed.

Lemma vec_change_hd {T : Type} {n} {w : Vector.t T n} x y :
  vec_change (x ## w) (Fin.F1) y = y ## w.
Proof. done. Qed.

Definition vec_simpl :=
  (@vec_pos_append_L, @vec_pos_append_R, @vec_change_append_L, @vec_change_append_R, @vec_pos_cons, @vec_pos_hd, @vec_change_cons, @vec_change_hd).

End Facts.

Import Facts.
Import L (term, var, app, lam).

Lemma closed_many_app_nat_enc {s} ns : L_facts.closed s ->
  L_facts.closed (fold_left (fun s n => app s (nat_enc n)) ns s).
Proof.
  elim: ns s. { done. }
  move=> n ns IH s ? /=. apply: IH.
  by apply: L_facts.app_closed; [|apply: L_facts.closed_nat_enc].
Qed.

Lemma sss_terminates_mma_f_ind {T : Type} {n : nat} (f : T -> (mm_state n)) (P : nat * list (mm_instr (pos n))) (R : T -> Prop) :
  (forall t, out_code (fst (f t)) P -> R t) ->
  (forall t1, (forall t2, sss_progress (mma_sss (n:=n)) P (f t1) (f t2) -> R t2) -> R t1) ->
  forall t, sss_terminates (mma_sss (n:=n)) P (f t) -> R t.
Proof.
  move=> H1 H2 t. move Et: (f t) => st Hst.
  pose R' := fun st' => forall t', f t' = st' -> R t'.
  suff: R' st by apply.
  move: Hst. apply: sss_terminates_ind.
  - by apply: mma_defs.mma_sss_fun.
  - move=> st' Hst' t' Ht'. apply: H1. by rewrite Ht'.
  - move=> st1' Hst1' t1' Ht1'. apply: H2.
    move=> t2'. rewrite Ht1' => /Hst1'.
    by apply; [apply: subcode_refl|].
Qed.

Module Argument.
Section Construction.
(* relation *)
Context {k0: nat} {R: Vector.t nat k0 -> nat -> Prop}.
(* term which computes the relation *)
Context {s0 : term} {Hs0 : L_facts.closed s0}.
(* s0 computes R *)
Context {Hs0R : forall (v : Vector.t nat k0) m, R v m <-> eval (Vector.fold_left (fun s n => app s (nat_enc n)) s0 v) (nat_enc m)}.
(* s0 computes numerals *)
Context {H's0R : forall (v : Vector.t nat k0) o, eval (Vector.fold_left (fun s n => app s (nat_enc n)) s0 v) o -> exists m, o = nat_enc m}.

#[local] Notation num_counters := ((1+k0)+6).
#[local] Notation counter := (pos num_counters).
#[local] Notation mm_instr := (mm_instr counter).

#[local] Notation "P // s ->> t" := (sss_compute (@mma_sss num_counters) P s t).
#[local] Notation "P // s -+> t" := (sss_progress (@mma_sss num_counters) P s t).
#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

#[local] Arguments vec_change_neq {X n v p q x}.
#[local] Arguments vec_change_eq {X n v p q x}.
#[local] Arguments vec_change_comm {X n v p q x y}.
#[local] Arguments Nat.pow : simpl never.
#[local] Arguments flatten : simpl never.

(* auxiliary counters *)
#[local] Notation A := (Fin.R (1+k0) (Fin.F1) : counter).
#[local] Notation B := (Fin.R (1+k0) (Fin.FS (Fin.F1)) : counter).
#[local] Notation C := (Fin.R (1+k0) (Fin.FS (Fin.FS (Fin.F1))) : counter).
(* data counters *)
#[local] Notation TS := (Fin.R (1+k0) (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) : counter).
#[local] Notation CTX := (Fin.R (1+k0) (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))) : counter).
#[local] Notation U := (Fin.R (1+k0) (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))))) : counter).

Lemma sss_terminates_sss_compute_inv P x y :
  P // x ->> y ->
  sss_terminates (mma_sss (n:=num_counters)) P x ->
  sss_terminates (mma_sss (n:=num_counters)) P y.
Proof.
  move=> ? [st] [Hx ?]. exists st. split; [|done].
  apply: sss_compute_inv; [|eassumption..].
  by apply: mma_defs.mma_sss_fun.
Qed.

#[local] Arguments plus : simpl never.

Definition enc_pair (m n: nat) := (n+n+1)*(2^m).

Fixpoint enc_term (s: term) : nat :=
  match s with
  | var n => enc_pair 0 n
  | lam s => enc_pair 1 (enc_term s)
  | app s t => enc_pair (2 + enc_term t) (enc_term s)
  end.

Definition enc_bool (b: bool) : nat :=
  if b then 1 else 0.

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

Definition enc_future (u: bool * eterm) :=
  match u with
  | (b, x) => enc_pair (enc_bool b) (enc_closure x)
  end.

Definition enc_vs vs := enc_list (map enc_future vs).
Arguments enc_vs !vs /.

#[local] Opaque PACK PACK_len UNPACK UNPACK_len.

(*
machine_var_0 x xs vs y :
  machine x vs y ->
  machine (closure (x :: xs) (var 0)) vs y
*)
Definition CASE_VAR0_codes (p: nat) (offset : nat) : list (nat -> list mm_instr) :=
  UNPACK A CTX U ::
  ZERO CTX ::
  JMP A p :: [].

Definition CASE_VAR0 p offset := compose (CASE_VAR0_codes p offset) offset.

Definition CASE_VAR0_len := UNPACK_len+ZERO_len+JMP_len.

#[local] Hint Extern 0 (Fin.R _ _ <> Fin.R _ _) => by move=> /R_inj : core.
#[local] Hint Extern 0 (vec_pos (Vector.append _ _) (Fin.R _ _) = _) => by rewrite vec_pos_append_R : core.

Lemma CASE_VAR0_spec vs x ctx p w offset :
  (offset, CASE_VAR0 p offset) // (offset, Vector.append w (0##0##0##enc_vs vs##enc_cs (x :: ctx)##0##vec_nil)) ->>
    (p, Vector.append w (0##0##0##enc_vs vs##0##(enc_closure x)##vec_nil)).
Proof.
  rewrite [enc_cs _]/=.
  apply: (compose_sss_compute_trans 0). { by apply: UNPACK_spec. }
  apply: (compose_sss_compute_trans 1). { by apply: ZERO_spec. }
  apply: (compose_sss_compute_trans 2). { by apply: JMP_spec. }
  rewrite !vec_simpl. by apply: sss_compute_refl.
Qed.

(*
machine_var_S x xs n vs y :
  machine (closure xs (var n)) vs y ->
  machine (closure (x :: xs) (var (S n))) vs y
*)
Definition CASE_VARS_codes (p: nat) (offset : nat) : list (nat -> list mm_instr) :=
  UNPACK A CTX B ::
  ZERO B ::
  PACK A U B ::
  PACK A U CTX ::
  JMP A p :: [].

Definition CASE_VARS p offset := compose (CASE_VARS_codes p offset) offset.

Definition CASE_VARS_len := UNPACK_len+ZERO_len+PACK_len+PACK_len+JMP_len.

Lemma CASE_VARS_spec vs u ctx n p w offset :
  (offset, CASE_VARS p offset) // (offset, Vector.append w (0##0##0##enc_vs vs##enc_cs (u :: ctx)##n##vec_nil)) ->>
    (p, Vector.append w (0##0##0##enc_vs vs##0##(enc_closure (closure ctx (var n)))##vec_nil)).
Proof.
  rewrite [enc_cs _]/=.
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 4). { by apply: JMP_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

(*
machine_app xs s t vs y :
  machine (closure xs s) ((true, (closure xs t)) :: vs) y ->
  machine (closure xs (app s t)) vs y
*)
Definition CASE_APP_codes (p: nat) (offset : nat) : list (nat -> list mm_instr) :=
  ZERO A ::
  ZERO C ::
  MOVE CTX A ::
  MOVE2 A CTX C ::
  PACK A U CTX ::
  PACK A B C ::
  INC C ::
  PACK A B C ::
  PACK A TS B ::
  JMP A p :: [].

Definition CASE_APP p offset := compose (CASE_APP_codes p offset) offset.

Definition CASE_APP_len := ZERO_len+ZERO_len+MOVE_len+MOVE2_len+PACK_len+PACK_len+INC_len+PACK_len+PACK_len+JMP_len.

#[local] Arguments enc_future : simpl never.

Lemma CASE_APP_spec vs ctx s t p w offset :
  (offset, CASE_APP p offset) // (offset, Vector.append w (0##enc_term t##0##enc_vs vs##enc_cs ctx##enc_term s##vec_nil)) ->>
    (p, Vector.append w (0##0##0##enc_vs ((true, closure ctx t) :: vs)##0##enc_closure (closure ctx s)##vec_nil)).
Proof.
  rewrite [enc_vs (_ :: _)]/=.
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: MOVE_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: MOVE2_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 4). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 5). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 6). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 7). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 8). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 9). { by apply: JMP_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

(*
machine_lam_swap xs s z vs y :
  machine z ((false, (closure xs s)) :: vs) y ->
  machine (closure xs (lam s)) ((true, z) :: vs) y
*)
Definition CASE_LAM_SWAP_codes (p: nat) (offset : nat) : list (nat -> list mm_instr) :=
  PACK A U CTX ::
  PACK A U CTX ::
  PACK A TS U ::
  MOVE B U ::
  ZERO C ::
  JMP A p :: [].

Definition CASE_LAM_SWAP p offset := compose (CASE_LAM_SWAP_codes p offset) offset.

Definition CASE_LAM_SWAP_len := PACK_len+PACK_len+PACK_len+MOVE_len+ZERO_len+JMP_len.

Lemma CASE_LAM_SWAP_spec n s vs ctx p w offset :
  (offset, CASE_LAM_SWAP p offset) // (offset, Vector.append w (0##n##0##enc_vs vs##enc_cs ctx##enc_term s##vec_nil)) ->>
    (p, Vector.append w (0##0##0##enc_vs ((false, closure ctx s) :: vs)##0##n##vec_nil)).
Proof.
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: MOVE_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 4). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 5). { by apply: JMP_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

(*
machine_lam_subst xss xts s t vs y :
  machine (closure ((closure xts (lam t)) :: xss) s) vs y ->
  machine (closure xts (lam t)) ((false, (closure xss s)) :: vs) y
*)
Definition CASE_LAM_SUBST_codes (p: nat) (offset : nat) : list (nat -> list mm_instr) :=
  ZERO C ::
  INC C ::
  PACK A U C ::
  PACK A U CTX ::
  UNPACK A B CTX ::
  PACK A CTX U ::
  PACK A B CTX ::
  MOVE B U ::
  JMP A p :: [].

Definition CASE_LAM_SUBST p offset := compose (CASE_LAM_SUBST_codes p offset) offset.

Definition CASE_LAM_SUBST_len := ZERO_len+INC_len+PACK_len+PACK_len+UNPACK_len+PACK_len+PACK_len+MOVE_len+JMP_len.

Lemma CASE_LAM_SUBST_spec n vs s t xts xss p w offset :
  (offset, CASE_LAM_SUBST p offset) // (offset, Vector.append w (0##enc_closure (closure xss s)##n##enc_vs vs##enc_cs xts##enc_term t##vec_nil)) ->>
    (p, Vector.append w (0##0##0##enc_vs vs##0##enc_closure (closure ((closure xts (lam t)) :: xss) s)##vec_nil)).
Proof.
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 4). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 5). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 6). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 7). { by apply: MOVE_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 8). { by apply: JMP_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

Definition CASE_LAM_codes (p q: nat) (offset : nat) : list (nat -> list mm_instr) :=
  JZ TS ((JZ_len+UNPACK_len+UNPACK_len+DEC_len+CASE_LAM_SUBST_len+CASE_LAM_SWAP_len)+offset) ::
  UNPACK A TS B ::
  UNPACK A B C ::
  DEC C ((JZ_len+UNPACK_len+UNPACK_len+DEC_len+CASE_LAM_SUBST_len) + offset) ::
  CASE_LAM_SUBST p ::
  CASE_LAM_SWAP p :: 
  INC TS ::
  PACK A U TS ::
  JMP A q :: [].

Definition CASE_LAM p q offset := compose (CASE_LAM_codes p q offset) offset.

Definition CASE_LAM_len := JZ_len+UNPACK_len+UNPACK_len+DEC_len+CASE_LAM_SUBST_len+CASE_LAM_SWAP_len+INC_len+PACK_len+JMP_len.

Lemma CASE_LAM_nil_spec p q w offset n s :
  (offset, CASE_LAM p q offset) // (offset, Vector.append w (0##0##0##0##n##enc_term s##vec_nil)) ->>
    (q, Vector.append w (0##0##0##0##n##enc_term (lam s)##vec_nil)).
Proof.
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: JZ_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 6). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 7). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 8). { by apply: JMP_spec. }
  by apply: sss_compute_refl.
Qed.

Lemma enc_pair_match {T : Type} {P Q : T} n m :
  match enc_pair n m with
  | 0 => P
  | S _ => Q
  end = Q.
Proof.
  have ? := Nat.pow_nonzero 2 n.
  suff: enc_pair n m = S (enc_pair n m - 1) by move=> ->.
  rewrite /enc_pair. nia.
Qed.

Lemma CASE_LAM_SUBST'_spec p q w s xss t xts vs offset :
  (offset, CASE_LAM p q offset) // (offset, Vector.append w (0##0##0##enc_vs ((false, (closure xss s)) :: vs)##enc_cs xts##enc_term t##vec_nil)) ->>
    (p, Vector.append w (0##0##0##enc_vs vs##0##enc_closure (closure ((closure xts (lam t)) :: xss) s)##vec_nil)).
Proof.
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: JZ_spec. }
  rewrite ?vec_simpl enc_pair_match. apply: (compose_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 4). { by apply: CASE_LAM_SUBST_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

Lemma CASE_LAM_SWAP'_spec p q w s xs z vs offset :
  (offset, CASE_LAM p q offset) // (offset, Vector.append w (0##0##0##enc_vs ((true, z) :: vs)##enc_cs xs##enc_term s##vec_nil)) ->>
    (p, Vector.append w (0##0##0##enc_vs ((false, closure xs s) :: vs)##0##enc_closure z##vec_nil)).
Proof.
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: JZ_spec. }
  rewrite ?vec_simpl enc_pair_match. apply: (compose_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 5). { rewrite ?vec_simpl. by apply: CASE_LAM_SWAP_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

(* compute natural number k for a (closure of a) Scott-encoded numeral k *)
Inductive decode_nat : list eterm -> term -> nat -> Prop :=
  | decode_nat_var n :
      decode_nat [] (var n) 0
  | decode_nat_var0 k xs' s' xs :
      decode_nat xs' s' k ->
      decode_nat ((closure xs' s') :: xs) (var 0) k
  | decode_nat_varS k n x xs :
      decode_nat xs (var n) k ->
      decode_nat (x :: xs) (var (S n)) k
  | decode_nat_lam k s xs :
      decode_nat ((closure [] (var 0)) :: xs) s k ->
      decode_nat xs (lam s) k
  | decode_nat_app xs s t k :
      decode_nat xs t k ->
      decode_nat xs (app s t) (S k).

Definition DECODE_NAT_codes (offset : nat) : list (nat -> list mm_instr) :=
  let delta_var := JZ_len+DEC_len+UNPACK_len+UNPACK_len+JMP_len+UNPACK_len+ZERO_len+PACK_len+JMP_len in
  let delta_lam := PACK_len+PACK_len+PACK_len+JMP_len in
  let delta_app := INC_len+ZERO_len+MOVE_len+JMP_len in
  UNPACK A U B ::
  DEC B ((UNPACK_len+DEC_len+delta_var) + offset) ::
  (* var _ CASE *) JZ CTX ((UNPACK_len+DEC_len+delta_var+DEC_len+delta_lam+delta_app)+offset) :: (* termination condition: (closure [] (var n)) *)
  DEC U ((UNPACK_len+DEC_len+JZ_len+DEC_len+UNPACK_len+UNPACK_len+JMP_len)+offset) ::
  (* var 0 CASE *) UNPACK A CTX U ::
  UNPACK A U CTX ::
  JMP A offset ::
  (* var (S n) CASE *) UNPACK A CTX B ::
  ZERO B ::
  PACK A U B ::
  JMP A offset ::
  DEC B ((UNPACK_len+DEC_len+delta_var+DEC_len+delta_lam)+offset) ::
  (* lam s CASE *) PACK A B C ::
  PACK A B C ::
  PACK A CTX B ::
  JMP A offset ::
  (* app s t CASE *) INC TS ::
  ZERO U ::
  MOVE B U ::
  JMP A offset :: 
  ZERO CTX ::
  ZERO U :: [].

Definition DECODE_NAT offset := compose (DECODE_NAT_codes offset) offset.

Definition DECODE_NAT_len := 
  let delta_var := JZ_len+DEC_len+UNPACK_len+UNPACK_len+JMP_len+UNPACK_len+ZERO_len+PACK_len+JMP_len in
  let delta_lam := PACK_len+PACK_len+PACK_len+JMP_len in
  let delta_app := INC_len+ZERO_len+MOVE_len+JMP_len in
  UNPACK_len+DEC_len+delta_var+DEC_len+delta_lam+delta_app+ZERO_len+ZERO_len.

(* app depth to the right *)
Fixpoint app_depth_r (s : term) : nat :=
  match s with
  | var _ => 0
  | app _ t => S (app_depth_r t)
  | lam s => app_depth_r s
  end.

Lemma app_depth_r_subst_many_repeat n s ts :
  app_depth_r (subst_many s n ts) = app_depth_r (subst_many s 0 ((repeat (var 0) n) ++ ts)).
Proof.
  elim: s n ts.
  - move=> x n ts /=.
    have [?|?] : x < n \/ n <= x by lia.
    + rewrite app_nth1. { by rewrite map_length seq_length. }
      rewrite app_nth1. { by rewrite repeat_length. }
      rewrite map_nth (@nth_indep _ _ x (var x) (var 0)). { by rewrite repeat_length. }
      by rewrite nth_repeat seq_nth.
    + rewrite app_nth2 map_length seq_length. { done. }
      by rewrite app_nth2 repeat_length.
  - by move=> ? _ ? + ?? /= => ->.
  - move=> s IH n ts /=.
    by rewrite [LHS]IH [RHS]IH app_assoc -repeat_app.
Qed.

Lemma app_depth_r_var_S x xs n :
  app_depth_r (flatten (closure (x :: xs) (var (S n)))) = app_depth_r (flatten (closure xs (var n))).
Proof.
  rewrite !flatten_var /=.
  have [Hn|Hn] : n < length (map flatten xs) \/ length (map flatten xs) <= n by lia.
  - by rewrite (nth_indep _ (var (S n)) (var n) Hn).
  - by rewrite !(nth_overflow _ _ Hn).
Qed.

Lemma app_depth_r_lam xs s :
  app_depth_r (flatten (closure xs (lam s))) = app_depth_r (flatten (closure (closure [] (var 0) :: xs) s)).
Proof.
  by rewrite /= app_depth_r_subst_many_repeat.
Qed.

Lemma decode_nat_app_depth_r xs s : decode_nat xs s (app_depth_r (flatten (closure xs s))).
Proof.
  move E: (closure xs s) => y.
  elim /(induction_ltof1 _ eterm_size) : y xs s E.
  rewrite /ltof. move=> [xs [n|s t|s]] IH ?? [-> ->].
  - move: xs IH => [|x xs].
    + move=> ?. rewrite flatten_term. by apply: decode_nat_var.
    + move: n => [|n].
      * move: x => [xs' x'] IH. apply: decode_nat_var0.
        rewrite flatten_var. apply: IH; [|done].
        rewrite /=. lia.
      * move=> IH. apply: decode_nat_varS.
        rewrite app_depth_r_var_S.
        apply: IH; [|done]. rewrite /=. lia.
  - rewrite flatten_app /=. apply: decode_nat_app. apply: IH; [|done].
    rewrite /=. lia.
  - apply: decode_nat_lam. rewrite app_depth_r_lam. 
    apply: IH; [|done]. rewrite /=. lia.
Qed.

Lemma decode_nat_nat_enc xs s n : flatten (closure xs s) = L.nat_enc n -> decode_nat xs s n.
Proof.
  intros Hn. have := decode_nat_app_depth_r xs s.
  congr decode_nat. rewrite Hn.
  clear Hn. by elim: n => *; [|congr S].
Qed.

Lemma DECODE_NAT_spec offset n xs s k w :
  flatten (closure xs s) = L.nat_enc n ->
  (offset, DECODE_NAT offset) // (offset, Vector.append w (0 ## 0 ## 0 ## k ## enc_cs xs ## enc_term s ## vec_nil)) ->>
    (DECODE_NAT_len+offset, Vector.append w (0 ## 0 ## 0 ## k+n ## 0 ## 0 ## vec_nil)).
Proof.
  rewrite /DECODE_NAT. move=> /decode_nat_nat_enc H. elim: H k.
  - move=> >.
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: UNPACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: DEC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: JZ_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 20). { by apply: ZERO_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 21). { by apply: ZERO_spec. }
    rewrite ?vec_simpl Nat.add_0_r. by apply: sss_compute_refl.
  - move=> > _ IH ?.
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: UNPACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: DEC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: JZ_spec. }
    rewrite ?vec_simpl enc_pair_match. apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 4). { by apply: UNPACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 5). { by apply: UNPACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 6). { by apply: JMP_spec. }
    by apply: IH.
  - move=> > _ IH ?.
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: UNPACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: DEC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: JZ_spec. }
    rewrite ?vec_simpl enc_pair_match. apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 7). { by apply: UNPACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 8). { by apply: ZERO_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 9). { by apply: PACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 10). { by apply: JMP_spec. }
    by apply: IH.
  - move=> > _ IH ?.
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: UNPACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: DEC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 11). { by apply: DEC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 12). { by apply: PACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 13). { by apply: PACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 14). { by apply: PACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 15). { by apply: JMP_spec. }
    by apply: IH.
  - move=> > _ IH k.
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: UNPACK_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: DEC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 11). { by apply: DEC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 16). { by apply: INC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 17). { by apply: ZERO_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 18). { by apply: MOVE_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 19). { by apply: JMP_spec. }
    rewrite -/enc_term -(Nat.add_succ_comm k). by apply: IH.
Qed.

(* main simulation routine; by case analysis on current term *)
(* U stores the current closure, TS stores the futures *)
(* on success decode resulting Scott numeral into pos0 *)
Definition PROG_codes (offset : nat) : list (nat -> list mm_instr) :=
  ZERO A ::
  UNPACK A U CTX ::
  UNPACK A U B ::
  DEC B ((ZERO_len+UNPACK_len+UNPACK_len+DEC_len+DEC_len+CASE_VAR0_len+CASE_VARS_len)+offset) ::
  (* var _ CASE *) DEC U ((ZERO_len+UNPACK_len+UNPACK_len+DEC_len+DEC_len+CASE_VAR0_len)+offset) ::
  (* var 0 CASE *) CASE_VAR0 offset ::
  (* var (S n) CASE *) CASE_VARS offset ::
  DEC B ((ZERO_len+UNPACK_len+UNPACK_len+DEC_len+DEC_len+CASE_VAR0_len+CASE_VARS_len+DEC_len+CASE_LAM_len)+offset) ::
  (* lam s CASE *) CASE_LAM offset ((ZERO_len+UNPACK_len+UNPACK_len+DEC_len+DEC_len+CASE_VAR0_len+CASE_VARS_len+DEC_len+CASE_LAM_len+CASE_APP_len)+offset) ::
  (* app s t CASE *) CASE_APP offset ::
  DECODE_NAT ::
  ZERO Fin.F1 ::
  MOVE TS Fin.F1 :: [].

Definition PROG offset := compose (PROG_codes offset) offset.

Definition PROG_len := ZERO_len+UNPACK_len+UNPACK_len+DEC_len+DEC_len+CASE_VAR0_len+CASE_VARS_len+DEC_len+CASE_LAM_len+CASE_APP_len+DECODE_NAT_len+ZERO_len+MOVE_len.

Lemma PROG_len_spec offset : length (PROG offset) = PROG_len.
Proof. done. Qed.

#[local] Opaque PROG.

Lemma ZERO_spec' X v offset : (offset, ZERO X offset) // (offset, v) -+> (ZERO_len + offset, vec_change v X 0).
Proof.
  have [[|k]] := ZERO_spec X v offset.
  - move=> /sss_steps_0_inv /(f_equal fst) /=. rewrite /ZERO_len /DEC_len. lia.
  - move=> Hk. exists (S k). by split; [lia|].
Qed.

(*
machine_var_0 x xs vs y :
  machine x vs y ->
  machine (closure (x :: xs) (var 0)) vs y
*)
Lemma PROG_VAR0_spec offset vs x xs w :
  (offset, PROG offset) //
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs vs ## 0 ## enc_closure (closure (x :: xs) (var 0)) ## vec_nil)) -+>
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs vs ## 0 ## enc_closure x ## vec_nil)).
Proof.
  rewrite [enc_closure _]/=.
  rewrite ?vec_simpl. apply: (compose_sss_progress_trans 0). { by apply: ZERO_spec'. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 4). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 5). { by apply: CASE_VAR0_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

(*
machine_var_S x xs n vs y :
  machine (closure xs (var n)) vs y ->
  machine (closure (x :: xs) (var (S n))) vs y
*)
Lemma PROG_VARS_spec offset vs x xs n w :
  (offset, PROG offset) //
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs vs ## 0 ## enc_closure (closure (x :: xs) (var (S n))) ## vec_nil)) -+>
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs vs ## 0 ## enc_closure (closure xs (var n)) ## vec_nil)).
Proof.
  rewrite ?vec_simpl. apply: (compose_sss_progress_trans 0). { by apply: ZERO_spec'. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 4). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 6). { by apply: CASE_VARS_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

(*
machine_app xs s t vs y :
  machine (closure xs s) ((true, (closure xs t)) :: vs) y ->
  machine (closure xs (app s t)) vs y
*)
Lemma PROG_APP_spec offset vs xs s t w :
  (offset, PROG offset) //
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs vs ## 0 ## enc_closure (closure xs (app s t)) ## vec_nil)) -+>
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs ((true, (closure xs t)) :: vs) ## 0 ## enc_closure (closure xs s) ## vec_nil)).
Proof.
  rewrite [enc_vs (_ :: _)]/=.
  rewrite ?vec_simpl. apply: (compose_sss_progress_trans 0). { by apply: ZERO_spec'. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 7). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 9). { by apply: CASE_APP_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

(*
machine_lam_swap xs s z vs y :
  machine z ((false, (closure xs s)) :: vs) y ->
  machine (closure xs (lam s)) ((true, z) :: vs) y
*)
Lemma PROG_LAM_SWAP_spec offset vs xs s z w :
  (offset, PROG offset) //
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs ((true, z) :: vs) ## 0 ## enc_closure (closure xs (lam s)) ## vec_nil)) -+>
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs ((false, (closure xs s)) :: vs) ## 0 ## enc_closure z ## vec_nil)).
Proof.
  rewrite ![enc_vs (_ :: _)]/=.
  rewrite ?vec_simpl. apply: (compose_sss_progress_trans 0). { by apply: ZERO_spec'. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 7). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 8). { by apply: CASE_LAM_SWAP'_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

(*
machine_lam_subst xss xts s t vs y :
  machine (closure ((closure xts (lam t)) :: xss) s) vs y ->
  machine (closure xts (lam t)) ((false, (closure xss s)) :: vs) y
*)
Lemma PROG_LAM_SUBST_spec offset vs xss xts s t w :
  (offset, PROG offset) //
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs ((false, (closure xss s)) :: vs) ## 0 ## enc_closure (closure xts (lam t)) ## vec_nil)) -+>
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs vs ## 0 ## enc_closure (closure ((closure xts (lam t)) :: xss) s) ## vec_nil)).
Proof.
  rewrite ?vec_simpl. apply: (compose_sss_progress_trans 0). { by apply: ZERO_spec'. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 7). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 8). { by apply: CASE_LAM_SUBST'_spec. }
  rewrite ?vec_simpl. by apply: sss_compute_refl.
Qed.

(*
machine_lam xs s :
  machine (closure xs (lam s)) nil (closure xs (lam s)).
*)
Lemma PROG_LAM_spec offset xs s n w :
  flatten (closure xs (lam s)) = L.nat_enc n ->
  (offset, PROG offset) //
  (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs [] ## 0 ## enc_closure (closure xs (lam s)) ## vec_nil)) ->>
  (PROG_len+offset, vec_change (Vector.append w vec_zero) Fin.F1 n).
Proof.
  move=> Hn.
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 7). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 8). { by apply: CASE_LAM_nil_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 10). { apply: DECODE_NAT_spec. exact: Hn. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 11). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 12). { by apply: MOVE_spec. }
  apply: sss_compute_refl'. congr pair. by rewrite (Vector.eta w) /= ?vec_simpl.
Qed.

Lemma PROG_simulation offset x vs y n w : machine x vs y -> flatten y = L.nat_enc n ->
  (offset, PROG offset) //
    (offset, Vector.append w (0 ## 0 ## 0 ## enc_vs vs ## 0 ## enc_closure x ## vec_nil)) ->>
    (PROG_len+offset, vec_change (Vector.append w vec_zero) Fin.F1 n).
Proof.
  elim=> > ?; [..|by apply: PROG_LAM_spec] => IH ?.
  all: apply: sss_compute_trans; [|by apply: IH].
  all: apply: sss_progress_compute.
  - by apply: PROG_VAR0_spec.
  - by apply: PROG_VARS_spec.
  - by apply: PROG_APP_spec.
  - by apply: PROG_LAM_SWAP_spec.
  - by apply: PROG_LAM_SUBST_spec.
Qed.

(*
  Scott-encoding of a given numeral n
  TS := n
  ~> U := encode_term (nat_enc n)
*)
Definition NAT_ENC_codes (p offset : nat) : list (nat -> list mm_instr) :=
  let loop := ZERO_len+ZERO_len+ZERO_len+INC_len+PACK_len+INC_len+PACK_len+INC_len+PACK_len in
  ZERO U ::
  ZERO B ::
  ZERO C ::
  INC U ::
  PACK A U B :: (* var 1 *)
  INC B ::
  PACK A U B :: (* lam (var 1) *)
  INC B ::
  PACK A U B :: (* lam (lam (var 1)) *)
  DEC TS ((loop+DEC_len+JMP_len)+offset) ::
  JMP A p ::
  ZERO B ::
  PACK A B C :: (* var 0 *)
  INC U ::
  INC U ::
  PACK A B U :: (* app (var 0) s *)
  MOVE B U ::
  INC B ::
  PACK A U B :: (* lam (app (var 0) s) *)
  INC B ::
  PACK A U B :: (* lam (lam (app (var 0) s)) *)
  JMP A (loop+offset) :: [].

Definition NAT_ENC_len :=
  let loop := ZERO_len+ZERO_len+ZERO_len+INC_len+PACK_len+INC_len+PACK_len+INC_len+PACK_len in
  loop+DEC_len+JMP_len+ZERO_len+PACK_len+INC_len+INC_len+PACK_len+MOVE_len+INC_len+PACK_len+INC_len+PACK_len+JMP_len.

Definition NAT_ENC p offset := compose (NAT_ENC_codes p offset) offset.

Lemma NAT_ENC_spec offset p n c w :
  (offset, NAT_ENC p offset) //
  (offset, Vector.append w (0 ## 0 ## 0 ## n ## c ## 0 ## vec_nil)) ->>
  (p, Vector.append w (0 ## 0 ## 0 ## 0 ## c ## enc_term (L.nat_enc n) ## vec_nil)).
Proof.
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 1). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 4). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 5). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 6). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 7). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 8). { by apply: PACK_spec. }
  rewrite ?vec_simpl.
  suff : forall m, (offset, compose (NAT_ENC_codes p offset) offset) //
    ((ZERO_len+ZERO_len+ZERO_len+INC_len+PACK_len+INC_len+PACK_len+INC_len+PACK_len) + offset,
        Vector.append w (0 ## 0 ## 0 ## n ## c ## enc_term (L.nat_enc m) ## vec_nil)) ->>
    (p, Vector.append w (0 ## 0 ## 0 ## 0 ## c ## enc_term (L.nat_enc (m+n)) ## vec_nil)).
  { move=> /(_ 0). by apply. }
  elim: n.
  { move=> m.
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 9). { by apply: DEC_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 10). { by apply: JMP_spec. }
    rewrite Nat.add_0_r. by apply: sss_compute_refl. }
  move=> n IH m.
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 9). { by apply: DEC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 11). { by apply: ZERO_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 12). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 13). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 14). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 15). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 16). { by apply: MOVE_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 17). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 18). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 19). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 20). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 21). { by apply: JMP_spec. }
  rewrite -(Nat.add_succ_comm m n). by apply: (IH (S m)).
Qed.

(* 
  Initialization routine:
  U := s, CTX := [n1; ..; nm]
  ~> U = closure ([], s (nat_enc n1) .. (nat_enc nm))
*)
Definition INIT_codes offset : list (nat -> list mm_instr) :=
  JZ CTX ((JZ_len+UNPACK_len+PACK_len+NAT_ENC_len+INC_len+INC_len+UNPACK_len+PACK_len+MOVE_len+JMP_len)+offset) ::
  UNPACK A CTX TS ::
  PACK A CTX U ::
  NAT_ENC ((JZ_len+UNPACK_len+PACK_len+NAT_ENC_len)+offset) ::
  INC U ::
  INC U ::
  UNPACK A CTX B ::
  PACK A B U :: (* app s [n] *)
  MOVE B U ::
  JMP A offset :: 
  PACK A U B :: [].

Definition INIT_len := JZ_len+UNPACK_len+PACK_len+NAT_ENC_len+INC_len+INC_len+UNPACK_len+PACK_len+MOVE_len+JMP_len+PACK_len.

Definition INIT offset := compose (INIT_codes offset) offset.

Lemma INIT_spec offset ns s w :
  (offset, INIT offset) //
  (offset, Vector.append w (0 ## 0 ## 0 ## 0 ## enc_list ns ## enc_term s ## vec_nil)) ->>
  (INIT_len+offset, Vector.append w (0 ## 0 ## 0 ## 0 ## 0 ## enc_closure (closure [] (fold_left (fun s n => app s (L.nat_enc n)) ns s)) ## vec_nil)).
Proof.
  elim: ns s => [s|n ns IH s].
  { rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: JZ_spec. }
    rewrite ?vec_simpl. apply: (compose_sss_compute_trans 10). { by apply: PACK_spec. }
    rewrite ?vec_simpl. by apply: sss_compute_refl. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 0). { by apply: JZ_spec. }
  rewrite ?vec_simpl enc_pair_match. apply: (compose_sss_compute_trans 1). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 2). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 3). { by apply: NAT_ENC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 4). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 5). { by apply: INC_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 6). { by apply: UNPACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 7). { by apply: PACK_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 8). { by apply: MOVE_spec. }
  rewrite ?vec_simpl. apply: (compose_sss_compute_trans 9). { by apply: JMP_spec. }
  rewrite ?vec_simpl. by apply: (IH (app s (L.nat_enc n))).
Qed.

(* 
  Initialization routine:
  ~> TS := [n1 .. nm]
*)
Definition INIT_INPUT_codes (offset : nat) : list (nat -> list mm_instr) :=
  map (PACK Fin.F1 CTX) (map (Fin.L 6) (map Fin.FS (rev (pos_list k0)))).

Definition INIT_INPUT_len := k0*PACK_len.

Definition INIT_INPUT offset := compose (INIT_INPUT_codes offset) offset.

Lemma INIT_INPUT_len_spec {offset} : length (INIT_INPUT offset) = INIT_INPUT_len.
Proof.
  rewrite /INIT_INPUT /INIT_INPUT_codes (length_compose (lengths := repeat PACK_len k0)).
  - apply: Forall2_repeat.
    + by rewrite !map_length rev_length pos_list_length.
    + apply /Forall_map /Forall_map /Forall_map /Forall_forall => *.
      by apply: PACK_len_spec.
  - by rewrite list_sum_repeat.
Qed.

Lemma fold_left_vec_zero_eq {n : nat} {w : Vector.t nat n} ps :
  (forall i, not (In i ps) -> vec_pos w i = 0) ->
  fold_left (fun v i => vec_change v i 0) ps w = vec_zero.
Proof.
  elim: ps w.
  - move=> w Hw /=. apply: vec_pos_ext => ?.
    by rewrite vec_zero_spec Hw.
  - move=> i ps IH w Hips /=. apply: IH => j Hjps.
    have [->|?] := pos_eq_dec i j.
    + by rewrite vec_change_eq.
    + rewrite vec_change_neq //. apply: Hips. by case.
Qed.

Lemma INIT_INPUT_spec offset w v :
  vec_pos (Vector.append (0 ## w) v) CTX = 0 ->
  (offset, INIT_INPUT offset) //
  (offset, Vector.append (0 ## w) v) ->>
  (INIT_INPUT_len+offset, vec_change (Vector.append vec_zero v) CTX (enc_list (Vector.to_list w))).
Proof.
  suff: forall (ps : list (Fin.t k0)) offset ns (w : vec nat k0) v,
    vec_pos v pos4 = enc_list ns ->
    NoDup ps ->
    (offset, compose (map (PACK Fin.F1 CTX) (map (Fin.L 6) (map Fin.FS ps))) offset) //
    (offset, Vector.append (0 ## w) v) ->>
    ((PACK_len * (length ps)) + offset,
      Vector.append (0 ## fold_left (fun w i => vec_change w i 0) ps w) (vec_change v pos4 (enc_list ((map (vec_pos w) (rev ps)) ++ ns)))).
  { move=> + /[dup] Hv. rewrite ?vec_simpl.
    move=> /(_ _ offset nil w v) /[apply]. move=> /(_ (rev (pos_list k0))).
    apply: unnest. { apply: NoDup_rev. by apply: pos_list_NoDup. }
    congr sss_compute. congr pair.
    - rewrite /INIT_INPUT_len rev_length pos_list_length. lia.
    - rewrite ?vec_simpl in Hv.
      congr Vector.append.
      + rewrite fold_left_vec_zero_eq //.
        move=> i H. exfalso. apply: H.
        by have /In_rev := pos_list_prop i.
      + rewrite rev_involutive app_nil_r. congr vec_change. congr enc_list.
        rewrite map_pos_list_vec. by elim: w; [|move=> > /= ->]. }
  elim.
  { move=> *. cbn. apply: sss_compute_refl'. by rewrite vec_change_same'. }
  move=> i ps IH {}offset ns {}w {}v Hv /NoDup_cons_iff [Hi /IH {}IH].
  apply: (compose_sss_compute_trans 0). { apply: PACK_spec; [done..|]. apply: nesym. by apply: Fin_L_R_neq. }
  rewrite /=. apply: subcode_sss_compute. { by apply: subcode_right. }
  have := (IH (PACK_len+offset) (vec_pos w i :: ns) (vec_change w i 0) (vec_change v pos4 (enc_list (vec_pos w i :: ns)))).
  apply: unnest. { by rewrite vec_change_eq. }
  rewrite PACK_len_spec /= ?vec_simpl Hv. congr sss_compute.
  - congr pair. lia.
  - congr pair; [lia|].
    congr Vector.cons. congr Vector.append.
    rewrite vec_change_idem /= map_app /= -app_assoc /=.
    congr vec_change. congr enc_list. congr List.app.
    apply /map_ext_in_iff => j Hj. apply: vec_change_neq => ?.
    apply: Hi. apply /In_rev. by subst j.
Qed.

Definition INIT_s0_codes (offset : nat) : list (nat -> list mm_instr) :=
  repeat (INC U) (enc_term s0).

Definition INIT_s0_len := enc_term s0.

Definition INIT_s0 offset := compose (INIT_s0_codes offset) offset.

Lemma INIT_s0_len_spec {offset} : length (INIT_s0 offset) = INIT_s0_len.
Proof.
  rewrite /INIT_s0 /INIT_s0_codes /INIT_s0_len.
  elim: (enc_term s0) offset. { done. }
  move=> n IH offset /=. by rewrite IH.
Qed.

#[local] Arguments repeat_spec {A n x y}.

Lemma INIT_s0_spec offset v :
  vec_pos v U = 0 ->
  (offset, INIT_s0 offset) //
  (offset, v) ->>
  (INIT_s0_len+offset, vec_change v U (enc_term s0)).
Proof.
  suff : forall j m offset v, j <= m ->
    v#>Fin.R (1 + k0) pos5 = m-j ->
    (offset, compose (repeat (INC U) m) offset) //
    ((m-j)+offset, v) ->>
    (m + offset, vec_change v U m).
  { move=> /(_ (enc_term s0) (enc_term s0)). rewrite Nat.sub_diag. by apply. }
  elim. { move=> m {}offset {}v _. rewrite !Nat.sub_0_r => ?. apply: sss_compute_refl'. by rewrite vec_change_same'. }
  move=> j IH m {}offset {}v ? Hv.
  have EmSj : m - S j = length (compose (firstn (m - S j) (repeat (INC U) m)) offset).
  { rewrite (length_compose (lengths := repeat INC_len (m - S j))).
  - apply: Forall2_repeat. { rewrite firstn_length repeat_length. lia. }
    rewrite firstn_repeat. by apply /Forall_forall => ? /repeat_spec ->.
  - by rewrite list_sum_repeat /INC_len Nat.mul_1_r. }
  rewrite EmSj. apply: (compose_sss_compute_trans).
  { rewrite (nth_indep _ _ (INC U)). { rewrite repeat_length. lia. }
    rewrite nth_repeat. apply: INC_spec. }
  rewrite -EmSj.
  have -> : 1 + (m - S j + offset) = (m - j) + offset by lia.
  rewrite Hv. apply: sss_compute_trans.
  { apply: IH; [lia|]. by rewrite vec_change_eq; [|lia]. }
  rewrite vec_change_idem. by apply: sss_compute_refl.
Qed.

(*
  Overall computation:
  1) TS := [n1; ..; nk0]
  2) U := s0
  3) U := s0 n1 .. nk0
  4) U := closure [] (s0 n1 .. nk0)
  5) compute
*)
Definition COMPUTE_codes (offset : nat) : list (nat -> list mm_instr) :=
  INIT_INPUT ::
  INIT_s0 ::
  INIT ::
  PROG :: [].

Definition COMPUTE offset := compose (COMPUTE_codes offset) offset.

Definition COMPUTE_lengths :=
  [INIT_INPUT_len; INIT_s0_len; INIT_len; PROG_len].

Definition COMPUTE_len := list_sum COMPUTE_lengths.

Lemma COMPUTE_lengths_spec offset :
  Forall2 (fun c l => forall j, length (c j) = l) (COMPUTE_codes offset) COMPUTE_lengths.
Proof.
  by do 4 (constructor; [auto using INIT_INPUT_len_spec, INIT_s0_len_spec|]).
Qed.

Lemma COMPUTE_len_spec offset : length (COMPUTE offset) = COMPUTE_len.
Proof.
  apply: length_compose. by apply: COMPUTE_lengths_spec.
Qed.

Lemma list_sum_append l ls offset :
  l + (list_sum ls + offset) = list_sum (ls ++ [l]) + offset.
Proof.
  rewrite list_sum_app /=. lia.
Qed.

Lemma simulation_init offset w :
  (offset, COMPUTE offset) //
    (offset, Vector.append (0 ## w) vec_zero) ->>
    ((list_sum (firstn 3 COMPUTE_lengths))+offset, Vector.append vec_zero
      (0 ## 0 ## 0 ## 0 ## 0 ## enc_closure (closure [] (fold_left (fun s n => app s (L.nat_enc n)) (Vector.to_list w) s0)) ## vec_nil)).
Proof.
  have compose_trans := (compose_sss_compute_length_trans _ (COMPUTE_lengths_spec offset)).
  rewrite ?vec_simpl. apply: (compose_trans 0). { by apply: INIT_INPUT_spec. }
  rewrite ?vec_simpl list_sum_append. apply: (compose_trans 1). { by apply: INIT_s0_spec. }
  rewrite ?vec_simpl list_sum_append. apply: (compose_trans 2). { by apply: INIT_spec. }
  rewrite ?vec_simpl list_sum_append. by apply: sss_compute_refl.
Qed.

(*
   s n1 .. nk0 evaluates to n
=> COMPUTE [n1 .. nm] [s] ~> n
*)
Lemma simulation offset y n w :
  machine (closure [] (fold_left (fun s n => app s (L.nat_enc n)) (Vector.to_list w) s0)) [] y ->
  flatten y = L.nat_enc n ->
  (offset, COMPUTE offset) // (offset, Vector.append (0 ## w) vec_zero) ->> (COMPUTE_len+offset, n ## vec_zero).
Proof.
  move=> /PROG_simulation /[apply] HPROG.
  have compose_trans := (compose_sss_compute_length_trans _ (COMPUTE_lengths_spec offset)).
  apply: sss_compute_trans. { by apply: simulation_init. }
  rewrite ?vec_simpl. apply: (compose_trans 3). { by apply: HPROG. }
  rewrite list_sum_append. apply: sss_compute_refl'. congr pair.
  rewrite (vec_zero_S k0) /=. congr Vector.cons.
  clear. by elim: (k0) => [|k IH]; [|rewrite /= IH].
Qed.

Lemma sss_terminates_PROG_machine offset vs x :
  sss_terminates (mma_sss (n:=num_counters)) (offset, PROG offset)
    (offset, Vector.append vec_zero
      (0 ## 0 ## 0 ## enc_vs vs ## 0 ## enc_closure x ## vec_nil)) ->
  eclosed x ->
  Forall eclosed_future vs ->
  exists y, machine x vs y.
Proof.
  have H' : forall (P Q : eterm -> Prop), (forall y, P y -> Q y) -> (exists y, P y) -> exists y, Q y.
  { firstorder done. }
  pose f := fun t => (offset, Vector.append vec_zero (0 ## 0 ## 0 ## enc_vs (fst t) ## 0 ## enc_closure (snd t) ## vec_nil)).
  pose P := fun t => eclosed (snd t) -> Forall eclosed_future (fst t) -> exists y, machine (snd t) (fst t) y.
  suff : forall vs_x,
    sss_terminates (mma_sss (n:=num_counters)) (offset, PROG offset) (f _ vs_x) ->
    P vs_x by move=> /(_ (vs, x)).
  apply: sss_terminates_mma_f_ind.
  { move=> [{}vs {}x]. have := PROG_len_spec offset. move: (PROG offset) => ? /= ->.
    rewrite /PROG_len /DEC_len. by lia. }
  subst P. move=> [{}vs [xs [{}x|s t|s]]] /= IH.
  - move: x xs IH => [|x] [|z xs] /= IH.
    + move=> [/boundE] /=. lia.
    + have := PROG_VAR0_spec offset vs z xs vec_zero.
      move=> /(IH (vs, z)) /= {}IH [_] [/IH] {}IH _ /IH.
      apply: H' => ?. by apply: machine_var_0.
    + move=> [/boundE]. lia.
    + have := PROG_VARS_spec offset vs z xs x vec_zero.
      move=> /(IH (vs, (closure xs (var x)))) /= {}IH.
      move=> [/bound_var_S_iff] ? [??] /IH.
      apply: unnest. { done. }
      apply: H' => ?. by apply: machine_var_S.
  - have := PROG_APP_spec offset vs xs s t vec_zero.
    move=> /(IH (((true, closure xs t) :: vs), (closure xs s))) /= {}IH.
    move=> [/boundE [??]] ??. move: IH.
    apply: unnest. { done. }
    apply: unnest. { by constructor. }
    apply: H' => ?. by apply: machine_app.
  - move: vs IH => [|[[] z] vs] /= IH.
    + move=> *. eexists. by apply: machine_lam.
    + have := PROG_LAM_SWAP_spec offset vs xs s z vec_zero.
      move=> /(IH (((false, closure xs s) :: vs), z)) /= {}IH.
      move=> [??] /Forall_cons_iff [??].
      move: IH.
      apply: unnest. { done. }
      apply: unnest. { by constructor. }
      apply: H' => ?. by apply: machine_lam_swap.
    + move: z IH => [xs's s'] /= IH.
      have := PROG_LAM_SUBST_spec offset vs xs's xs s' s vec_zero.
      move=> /(IH (vs, closure (closure xs (lam s) :: xs's) s')) /= {}IH.
      move=> [??] /Forall_cons_iff [/= [/boundE ??] ?].
      move: IH.
      apply: unnest. { done. }
      apply: unnest. { done. }
      apply: H' => ?. by apply: machine_lam_subst.
Qed.

(* MMA termination implies L-evaluation *)
Lemma sss_terminates_COMPUTE_eval offset v :
  sss_terminates (mma_sss (n:=num_counters)) (offset, COMPUTE offset) (offset, Vector.append (0 ## v) vec_zero) ->
  exists t, eval (Vector.fold_left (fun (s : term) (n0 : nat) => app s (nat_enc n0)) s0 v) t.
Proof using Hs0.
  have := simulation_init offset v.
  move=> /sss_terminates_sss_compute_inv /[apply].
  move=> /subcode_sss_terminates.
  set i := list_sum (firstn 3 COMPUTE_lengths) + offset.
  move=> /(_ (i, PROG i)).
  apply: unnest.
  { apply: (subcode_nth_compose 3).
    rewrite (length_compose (lengths := firstn 3 COMPUTE_lengths)) //.
    apply: Forall2_firstn. by apply: COMPUTE_lengths_spec. }
  rewrite Vector.to_list_fold_left.
  move=> /(sss_terminates_PROG_machine _ nil _).
  apply: unnest. { split; [|done]. apply /L_facts.closed_dcl. by apply: closed_many_app_nat_enc. }
  apply: unnest. { done. }
  move=> [?] /wCBV.machine_inverse_simulation.
  apply: unnest. { split; [|done]. apply /L_facts.closed_dcl. by apply: closed_many_app_nat_enc.  }
  apply: unnest. { done. }
  rewrite flatten_term => ?. eexists. eassumption.
Qed.

Lemma MMA_computable_R : MMA_computable R.
Proof using Hs0 Hs0R H's0R.
  eexists _, (COMPUTE 1). move=> v m.
  have /wCBV.machine_correctness H := closed_many_app_nat_enc (Vector.to_list v) Hs0.
  split.
  - move=> /Hs0R. rewrite Vector.to_list_fold_left.
    move=> /H [y] [/simulation] /[apply] {}H.
    do 2 eexists. split. { by apply: H. }
    right. rewrite /= COMPUTE_len_spec. lia.
  - move=> [n] [v'] Hmv'. apply /Hs0R.
    rewrite Vector.to_list_fold_left. apply /H.
    apply /wCBV.machine_correctness. { by apply: closed_many_app_nat_enc. }
    have [t] : exists t, eval (Vector.fold_left (fun (s : term) (n : nat) => app s (nat_enc n)) s0 v) t.
    { apply: sss_terminates_COMPUTE_eval. eexists. by eassumption. }
    move=> /[dup] /H's0R [m' ->].
    rewrite Vector.to_list_fold_left.
    move=> Hm'. suff: m = m' by move ->.
    move: Hm' => /H [y] [/simulation] /[apply] /(_ 1) {}H.
    have : sss_output (mma_sss (n:=num_counters)) (1, COMPUTE 1)
      (1, Vector.append (0 ## v) vec_zero) (COMPUTE_len + 1, m' ## vec_zero).
    { split; [done|]. right. rewrite /= COMPUTE_len_spec. lia. }
    move: Hmv' (@mma_defs.mma_sss_fun num_counters) => /sss_output_fun /[apply] /[apply].
    by case.
Qed.

End Construction.
End Argument.

(* use L_computable_closed *)
From Undecidability Require
  TM.L.CompilerBoolFuns.ClosedLAdmissible.

Theorem L_computable_to_MMA_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  L_computable R -> MMA_computable R.
Proof.
  move=> /ClosedLAdmissible.L_computable_can_closed [s] [Hs] s_spec.
  apply: Argument.MMA_computable_R.
  - eassumption.
  - move=> v. by case: (s_spec v).
  - move=> v. by case: (s_spec v).
Qed.
