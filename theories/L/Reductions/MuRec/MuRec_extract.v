From Undecidability.L.Datatypes Require Import LNat LOptions LSum List.List_nat.
Require Import Undecidability.L.Tactics.GenEncode.
From Undecidability Require Import MuRec.Util.eval.

MetaRocq Run (tmGenEncode "enc_reccode" reccode).
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
