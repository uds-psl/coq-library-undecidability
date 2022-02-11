From Undecidability Require Import TM.SBTM2.
Require Import PeanoNat Lia List ssreflect ssrbool ssrfun.
Import ListNotations SBTM2Notations.

Lemma iter_plus {X} (f : X -> X) (x : X) n m : Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof.
  elim: m; first by rewrite Nat.add_0_r.
  move=> m /= <-. by have ->: n + S m = S n + m by lia.
Qed.

Lemma oiter_None {X : Type} (f : X -> option X) k : Nat.iter k (obind f) None = None.
Proof. elim: k; [done | by move=> /= ? ->]. Qed.

Lemma steps_plus {M} k1 k2 {x} :
  steps M (k1 + k2) x = obind (fun y => steps M k2 y) (steps M k1 x).
Proof.
  rewrite /steps iter_plus /=.
  move: (Nat.iter k1 _ (Some x)) => [y|] /=; first done.
  apply: oiter_None.
Qed.

Lemma steps_None_mono {M x} k2 k1 : steps M k1 x = None -> k1 <= k2 -> steps M k2 x = None.
Proof.
  elim: k2 k1 x.
  { move=> [|k1]; [done|lia]. }
  move=> k2 IH [|k1] x + ?; first done.
  rewrite (steps_plus 1 k1) (steps_plus 1 k2).
  move: (steps M 1 x) => [y|]; last done.
  move=> /IH. apply. lia.
Qed.

Lemma steps_sync {M k1 x k2 y} :
  steps M (S k1) x = None -> steps M (S k2) x = Some y -> steps M k1 y = None.
Proof.
  elim: k1 k2 x.
  { move=> k2 x. rewrite (steps_plus 1 k2). by move=> ->. }
  move=> k1 IH k2 x.
  rewrite (steps_plus 1 (S k1)) (steps_plus 1 k2).
  move: (steps M 1 x) => [z|]; last done.
  move: k2 => [|k2].
  { by move=> /= <- [<-]. }
  move=> /IH H /H /(steps_None_mono (S k1)). apply. lia.
Qed.

(* two lists are almost_eq if they differ only in trailing false symbols *)
Inductive almost_eq : list bool -> list bool -> Prop :=
  | almost_eq_cons a l1 l2 : almost_eq l1 l2 -> almost_eq (a :: l1) (a :: l2)
  | almost_eq_false n1 n2 : almost_eq (repeat false n1) (repeat false n2).

Inductive almost_eq_tape : tape -> tape -> Prop :=
  | almost_eq_tape_intro a ls1 rs1 ls2 rs2 :
      almost_eq ls1 ls2 -> almost_eq rs1 rs2 -> 
      almost_eq_tape (ls1, a, rs1) (ls2, a, rs2).

Lemma almost_eq_tape_step_Some M q q1 q2 t1 t'1 t2 t'2 :
  almost_eq_tape t1 t2 -> 
  step M (q, t1) = Some (q1, t'1) ->
  step M (q, t2) = Some (q2, t'2) ->
  q1 = q2 /\ almost_eq_tape t'1 t'2.
Proof.
  have ? := almost_eq_false 0 0.
  have ? := almost_eq_false 0 _.
  have ? := almost_eq_false _ 0.
  case=> a ???? [] => [????|n1 n2] [].
  - move=> ????. rewrite /step /=. case: (trans' M _); last done.
    move=> [[? ?] []] [] <- <- [] <- <- /=; by do ? constructor.
  - move=> n'1 n'2. rewrite /step /=. case: (trans' M _); last done.
    move=> [[? ?] []] [] <- <- [] <- <- /=; first by do ? constructor.
    move: n'1 n'2 => [|?] [|?] /=; by do ? constructor.
  - move=> ????. rewrite /step /=. case: (trans' M _); last done.
    move=> [[? ?] []] [] <- <- [] <- <- /=; last by do ? constructor.
    move: n1 n2 => [|?] [|?] /=; by do ? constructor.
  - move=> n'1 n'2. rewrite /step /=. case: (trans' M _); last done.
    move=> [[? ?] []] [] <- <- [] <- <- /=.
    + move: n1 n2 => [|?] [|?] /=; by do ? constructor.
    + move: n'1 n'2 => [|?] [|?] /=; by do ? constructor.
Qed.

Lemma almost_eq_tape_step_None M q t1 t2 :
  almost_eq_tape t1 t2 -> 
  step M (q, t1) = None ->
  step M (q, t2) = None.
Proof.
  case=> a ???? [] => [????|n1 n2] [] >.
  all: rewrite /step /=.
  all: case: (trans' M _); last done.
  all: by move=> [[? ?] ?].
Qed.

Lemma almost_eq_refl l : almost_eq l l.
Proof.
  elim: l => >.
  - by apply: (almost_eq_false 0 0).
  - by apply: almost_eq_cons.
Qed.

Lemma almost_eq_sym l1 l2 : almost_eq l1 l2 -> almost_eq l2 l1.
Proof. elim=> *; by constructor. Qed.

Lemma almost_eq_tape_sym t1 t2 : almost_eq_tape t1 t2 -> almost_eq_tape t2 t1.
Proof. move=> [] > /almost_eq_sym ? /almost_eq_sym ?. by constructor. Qed.

Lemma almost_eq_tape_steps_None {M k q t1 t2} :
  almost_eq_tape t1 t2 ->
  (steps M k (q, t1) = None <-> steps M k (q, t2) = None).
Proof.
  elim: k q t1 t2; first done.
  move=> k IH q t1 t2. rewrite !(steps_plus 1 k) /=.
  case E1: (step M (q, t1)) => [[q2 t'1]|];
    case E2: (step M (q, t2)) => [[q'2 t'2]|].
  - move: E1 E2 => /almost_eq_tape_step_Some /[apply] /[apply].
    move=> [<- /IH]. by apply.
  - move=> /almost_eq_tape_sym Ht2t1.
    by move: E2 Ht2t1 E1 => /almost_eq_tape_step_None /[apply] ->.
  - move=> Ht1t2.
    by move: E1 Ht1t2 E2 => /almost_eq_tape_step_None /[apply] ->.
  - done.
Qed.

Fixpoint seq_Vector (n : nat) : Vector.t (Fin.t n) n :=
  match n return Vector.t (Fin.t n) n with
  | 0 => Vector.nil (Fin.t 0)
  | S n' => Vector.cons (Fin.t (S n')) (Fin.F1) n' (Vector.map (Fin.R 1) (seq_Vector n'))
  end.

Lemma seq_Vector_spec {n} (q : Fin.t n) : 
  VectorDef.nth (seq_Vector n) q = q.
Proof.
  elim: q; first done.
  move=> {}n q IH /=. 
  by rewrite (Vector.nth_map _ _ q q erefl) IH.
Qed.

(* build transition table from transition function *)
Definition construct_trans {n : nat}
  (f : (Fin.t n) * bool -> option ((Fin.t n) * bool * direction)) :
  Vector.t (
    (option ((Fin.t n) * bool * direction)) *
    (option ((Fin.t n) * bool * direction))) n :=
  Vector.map (fun q => (f (q, true), f (q, false))) (seq_Vector n).

Lemma construct_trans_spec {n : nat} 
  (f : (Fin.t n) * bool -> option ((Fin.t n) * bool * direction)) :
  forall x, trans' (Build_SBTM2 n (construct_trans f)) x = f x.
Proof.
  move=> /= [q a]. rewrite /trans' /construct_trans /=.
  rewrite (Vector.nth_map _ _ q q erefl) seq_Vector_spec.
  by case: a.
Qed.
