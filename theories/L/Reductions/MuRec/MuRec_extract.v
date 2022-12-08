From Undecidability.L.Datatypes Require Import LNat LOptions LSum List.List_nat.
Require Import Undecidability.L.Tactics.GenEncode.

Inductive reccode :=
| rc_cst (n : nat)
| rc_zero
| rc_succ
| rc_proj (n : nat)
| rc_comp (f : reccode) (g : reccode)
| rc_cons (f : reccode) (g : reccode)
| rc_nil
| rc_rec (f : reccode) (g : reccode)
| rc_min (f : reccode).

Definition id_Some_inl (o : option (nat + list nat)) : option (nat + list nat) :=
  match o with
  | Some (inl f) => o
  | _ => None
  end.

#[global] Arguments id_Some_inl /.

Definition eval_rec (eval : nat -> reccode -> list nat -> option (nat + list nat)) (min : nat) (c : reccode) (v : list nat) : option (nat + list nat) :=
  match c with
  | rc_cst n => Some (inl n)
  | rc_zero => Some (inl 0)
  | rc_succ => match v with
              | x :: _ => Some (inl (S x))
              | _ => None
              end
  | rc_proj n => option_map inl (nth_error v n)
  | rc_comp f g => match eval min g v
                  with
                  | Some (inr g) => id_Some_inl (eval min f g)
                  | _ => None
                  end
  | rc_cons f g => match eval min f v, eval min g v with
                  | Some (inl f), Some (inr g) => Some (inr (f :: g))
                  | _, _ => None
                  end
  | rc_nil => Some (inr nil)
  | rc_rec f g => match v with
                  | 0 :: v => id_Some_inl (eval min f v)
                  | S n :: v => match eval min (rc_rec f g) (n :: v) with
                              | Some (inl y) => id_Some_inl (eval min g (n :: y :: v))
                              | _ => None
                              end
                  | _ => None
                  end
  | rc_min f => match eval 0 f (min :: v) with
                | Some (inl 0) => Some (inl min)
                | Some (inl _) => id_Some_inl (eval (S min) (rc_min f) v)
                | _ => None
                end
  end.

Fixpoint eval (fuel : nat) (min : nat) (c : reccode) (v : list nat) : option (nat + list nat) :=
  match fuel with
  | 0 => None
  | S fuel => eval_rec (eval fuel) min c v
  end.

MetaCoq Run (tmGenEncode "enc_reccode" reccode).
#[export] Hint Resolve enc_reccode_correct : Lrewrite.

#[global]
Instance term_rc_comp: computable rc_comp. Proof. extract constructor. Qed.
#[global]
Instance term_rc_cons : computable rc_cons. Proof. extract constructor. Qed.
#[global]
Instance term_rc_rec : computable rc_rec. Proof. extract constructor. Qed.
#[global]
Instance term_rc_min : computable rc_min. Proof. extract constructor. Qed.
#[local] Instance term_id_Some_inl : computable id_Some_inl.
Proof. extract. Qed.
#[local] Instance term_eval_rec : computable eval_rec.
Proof. extract. Qed.
#[global] Instance term_eval : computable eval.
Proof.
  extract.
Qed.
