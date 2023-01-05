From Undecidability.FOL.Semantics Require Import Tarski.FullFacts.
From Undecidability.FOL.Semantics Require Export FiniteTarski.Listability.
From Undecidability.FOL.Syntax Require Import Facts.
Require Import Undecidability.Synthetic.DecidabilityFacts.
Require Import Undecidability.Shared.Dec.
Require Import List.

Section DefaultSyntax. (* An alternative development of FSAT in Trakhtenbrot is "Trakhtenbrot Syntax" *)
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  (* Satisfiability in a finite and decidable model *)

  Definition FSAT (phi : form) :=
    exists D (I : interp D) rho, listable D /\ (forall p, decidable (fun v => i_atom (P:=p) v)) /\ rho ⊨ phi.

  (* Validity in a finite and decidable model *)

  Definition FVAL (phi : form) :=
    forall D (I : interp D) rho, listable D /\ (forall p, decidable (fun v => i_atom (P:=p) v)) -> rho ⊨ phi.


  (* Satisfiability in a discrete, finite, and decidable model *)

  Definition FSATd (phi : form) :=
    exists D (I : interp D) rho, listable D /\ discrete D /\ (forall p, decidable (fun v => i_atom (P:=p) v)) /\ rho ⊨ phi.

  (* Satisfiability in a discrete, finite, and decidable model restricted to closed formulas *)

  Definition cform := { phi | bounded 0 phi }.

  Definition FSATdc (phi : cform) :=
    FSATd (proj1_sig phi).
End DefaultSyntax.

Section decidable.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  (* Show satisfaction decidable for fixed model *)
  Lemma general_decider D (I:interp D) (e : env D) f : cListable D -> (forall (ff:falsity_flag) p v ee, dec (ee ⊨ atom p v)) -> dec (e ⊨ f).
  Proof.
  intros Hfin Hdec.
  induction f as [|f p v|f [] l IHl r IHr|f [] v IHv] in e|-*.
  - now right.
  - apply Hdec.
  - cbn. now apply and_dec.
  - cbn. now apply or_dec.
  - cbn. now apply impl_dec.
  - cbn. apply fin_dec. 1:easy. intros k. apply IHv.
  - cbn. apply fin_dec_ex. 1:easy. intros k. apply IHv.
  Qed.
End decidable.

