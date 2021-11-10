From Undecidability.L.Datatypes Require Import LNat Lists LOptions LSum.
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

Fixpoint eval (fuel : nat) (min : nat) (c : reccode) (v : list nat) : option (nat + list nat) :=
  match fuel with
  | 0 => None
  | S fuel =>
    match c with
    | rc_cst n => Some (inl n)
    | rc_zero => Some (inl 0)
    | rc_succ => match v with
                | x :: _ => Some (inl (S x))
                | _ => None
                end
    | rc_proj n => match nth_error v n with Some r => Some (inl r) | None => None end
    | rc_comp f g => match eval fuel min g v
                    with
                    | Some (inr g) => match eval fuel min f g with Some (inl f) => Some (inl f) | _ => None end
                    | _ => None
                    end
    | rc_cons f g => match eval fuel min f v, eval fuel min g v with
                    | Some (inl f), Some (inr g) => Some (inr (f :: g))
                    | _, _ => None
                    end
    | rc_nil => Some (inr nil)
    | rc_rec f g => match v with
                   | 0 :: v => match eval fuel min f v with Some (inl r) => Some (inl r) | _ => None end
                   | S n :: v => match eval fuel min (rc_rec f g) (n :: v) with
                               | Some (inl y) => match eval fuel min g (n :: y :: v) with Some (inl r) => Some (inl r) | _ => None end
                               | _ => None
                               end
                   | _ => None
                   end
    | rc_min f => match eval fuel 0 f (min :: v) with
                 | Some (inl 0) => Some (inl min)
                 | Some (inl _) => match eval fuel (S min) (rc_min f) v with Some (inl r) => Some (inl r) | _ => None end
                 | _ => None
                 end
    end
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
#[global]
Instance term_eval : computable eval.
Proof.
  extract.
Qed.
