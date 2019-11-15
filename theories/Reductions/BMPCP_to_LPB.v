(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Binary modified Post correspondence problem (BMPCP)
  to:
    Recognizing axiomatizations of Hilber-style calculi (LPB)

  References:
    [1] Grigoriy V. Bokov: Undecidable problems for propositional calculi with implication. 
      Logic Journal of the IGPL, 24(5):792–806, 2016. doi:10.1093/jigpal/jzw013
    [2] Andrej Dudenhefner, Jakob Rehof: Lower End of the Linial-Post Spectrum. 
      TYPES 2017: 2:1-2:15. doi: 10.4230/LIPIcs.TYPES.2017.2
*)

Require Import List.
Import ListNotations.
Require Import Psatz.
Require Import ssreflect ssrbool ssrfun. 

From Undecidability Require Import Problems.LPB.

Section Facts.

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  apply : well_founded_ind.
  apply : Wf_nat.well_founded_lt_compat. move => *. by eassumption.
Qed.
Arguments measure_ind {X}.

End Facts.

Section ForallNorm.

Variable T : Type.
Variable P : T -> Prop.

Lemma Forall_nilP : Forall P [] <-> True.
Proof. by constructor. Qed.

Lemma Forall_consP {a A} : Forall P (a :: A) <-> P a /\ Forall P A.
Proof.
  constructor. 
    move=> H. by inversion H.
  move=> [? ?]. by constructor.
Qed.

Lemma Forall_singletonP {a} : Forall P [a] <-> P a.
Proof. rewrite Forall_consP Forall_nilP. by tauto. Qed.

Lemma Forall_appP {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
  elim: A.
    constructor; by [|case].
  move=> ? ? IH /=. rewrite ? Forall_consP ? IH.
  by tauto.
Qed.

(* usage rewrite ? Forall_norm *)
Definition Forall_norm := (@Forall_appP, @Forall_singletonP, @Forall_consP, @Forall_nilP).

End ForallNorm.

Section ListFacts.

(* any list is empty or has a last element *)
Lemma nil_or_ex_last {T: Type} (A: list T) : A = [] \/ exists B a, A = B ++ [a].
Proof.
  elim: A.
    by left.
  move=> a A. case.
    move=> ->. right. by exists [], a.
  move=> [B [b ->]]. right. by exists (a :: B), b.
Qed.

(* induction wrt the last element of a list *)
Lemma list_last_ind (X: Type) (P : list X -> Prop) : 
  P [] ->
  (forall a A, P A -> P (A ++ [a])) ->
  forall (A : list X), P A.
Proof.
  move=> H1 H2. elim /(measure_ind (@length X)).
  move=> A IH. case: (nil_or_ex_last A).
    by move=> ->.
  move=> [B [a ?]]. subst A. apply: H2. apply: IH.
  rewrite app_length /length. by lia.
Qed.

Arguments list_last_ind [X].

Lemma incl_consP {X: Type} {a: X} {A B} : incl (a :: A) B <-> (In a B /\ incl A B).
Proof.
  by rewrite /incl - ? Forall_forall ?Forall_norm.
Qed.

End ListFacts.

Definition bullet := var 0.
(* encodes symbol true *)
Definition b2 := (arr bullet bullet).
(* encodes symbol false *)
Definition b3 := arr bullet (arr bullet bullet).

Fixpoint append_word (s: formula) (v: list bool) :=
  match v with
  | [] => s
  | a :: v => 
    if a then 
      append_word (arr b2 s) v else 
      append_word (arr b3 s) v
  end.

Definition encode_word (v: list bool) := append_word bullet v.
Definition encode_pair (s t: formula) := arr b3 (arr s (arr t b3)).

(*
Notation "⟨ s , t ⟩" := (encode_pair s t).
Notation "⟦ v ⟧" := (encode_word v).
Notation "s → t" := (arr s t) (at level 50).
*)

(* environment encoding the instance ((v, w), P) of BMPCP *)
Definition Γ v w P := 
  (encode_pair (var 1) (var 1)) :: 
  (arr (encode_pair (encode_word v) (encode_word w)) a_b_a) ::
  map (fun '(v, w) => arr (encode_pair (append_word (var 2) v) (append_word (var 3) w)) (encode_pair (var 2) (var 3))) ((v, w) :: P).

(* list of first k arguments *)
Fixpoint arguments (k: nat) (t: formula) :=
  match k with
  | 0 => []
  | S k => 
    match t with
    | var _ => []
    | arr s t => s :: (arguments k t)
    end
  end.

(* target after first k arguments *)
Fixpoint target (k: nat) (t: formula) :=
  match k with
  | 0 => t
  | S k => 
    match t with
    | var _ => t
    | arr _ t => target k t
    end
  end.

(* Hilbert-style calculus with derivation depth *)
Inductive der (Gamma: list formula) : nat -> formula -> Prop :=
  | der_var {ζ: nat -> formula} {s t: formula} {k n: nat} :
      In s Gamma -> 
      Forall (der Gamma n) (arguments k (substitute ζ s)) -> 
      target k (substitute ζ s) = t ->
      der Gamma (S n) t.

Lemma arr_allowed {s t} : hsc [a_b_a] t -> hsc [a_b_a] (arr s t).
Proof.
  move=> H. apply: hsc_arr; last by eassumption.
  pose ζ i := if i is 0 then t else if i is 1 then s else var i.
  have -> : arr t (arr s t) = substitute ζ a_b_a by done.
  apply: hsc_var. by left.
Qed.

Lemma b3_allowed : hsc [a_b_a] b3.
Proof.
  pose ζ i := if i is 0 then bullet else if i is 1 then bullet else var i.
  have -> : b3 = substitute ζ a_b_a by done.
  apply: hsc_var. by left.
Qed.

(* Γ v w P is derivable from a → b → a *)
Lemma Γ_allowed {v w P} : forall r, In r (Γ v w P) -> hsc [a_b_a] r.
Proof.
  rewrite - Forall_forall /Γ ? Forall_norm. constructor; last constructor; last constructor.
  - rewrite /encode_pair.
    do 3 (apply: arr_allowed). by apply: b3_allowed.
  - apply: arr_allowed.
    have -> : a_b_a = substitute var a_b_a by done.
    apply: hsc_var. by left.
  - rewrite /encode_pair.
    do 4 (apply: arr_allowed). by apply: b3_allowed.
  - rewrite Forall_forall => ?. rewrite in_map_iff => [[[x y]]] [<- _].
    rewrite /encode_pair.
    do 4 (apply: arr_allowed). by apply: b3_allowed.
Qed.

(* can be replaced by derE *)
Lemma der_0E {n Gamma t} : der Gamma n t -> n = S (Nat.pred n).
Proof. move=> H. by inversion H. Qed.

Lemma derE {n Gamma t} : der Gamma n t -> 
  exists (ζ: nat -> formula) (s: formula) (k: nat),
    n = S (Nat.pred n) /\
    In s Gamma /\
    Forall (der Gamma (Nat.pred n)) (arguments k (substitute ζ s)) /\
    target k (substitute ζ s) = t.
Proof.
  move=> H. inversion H. do 3 eexists. by eauto.
Qed.

Lemma der_mon {n m t Gamma} : der Gamma n t -> n <= m -> der Gamma m t.
Proof.
  elim: n m Gamma t.
    by move=> > /der_0E.
  move=> n IH m Gamma t.
    move /derE => [ζ [s' [k']]].
    move=> [_ [? [? ?]]] ?.
    have -> : m = S (Nat.pred m) by lia.
    apply: der_var; try eassumption.
    apply: Forall_impl; last by eassumption.
    move=> ? /IH. apply. by lia.
Qed.

Lemma target_S {r s t k} : target k r = arr s t -> target (S k) r = t.
Proof.
  elim: k r s t.
    by move=> > /= ->.
  move=> k IH. case.
    by move=> > /=.
  by move=> > /= /IH <-.
Qed.

Lemma arguments_S {r s t k} : target k r = arr s t -> arguments (S k) r = (arguments k r) ++ [s].
Proof.
  elim: k r s t.
    by move=> > /= ->.
  move=> k IH. case.
    by move=> > /=.
  by move=> > /= /IH <-.
Qed.

(* every hsc derivation has a depth *)
Lemma hsc_der {Gamma t} : hsc Gamma t -> exists n, der Gamma n t.
Proof.
  elim.
    move=> ζ s /der_var => /(_ ζ (substitute ζ s) 0 0).
    move /(_ ltac:(by constructor)). move /(_ ltac:(done)).
    move=> ?. by exists 1.
  move=> s' t' _ [n1 /derE +] _ [n2 /derE].
  move=> [ζ1 [s1 [k1 [-> [Hs1 [? Hk1]]]]]].
  move=> [ζ2 [s2 [k2 [-> [? [? ?]]]]]].
  exists (S (S (n1+n2))). apply: (der_var _ (ζ := ζ1) (s := s1) (k := S k1)).
    - done.
    - rewrite (arguments_S ltac:(eassumption)). rewrite ? Forall_norm. constructor.
        apply: Forall_impl; last eassumption.
        move=> ? /der_mon. apply. by lia.
      apply: der_var; last eassumption; first done.
      apply: Forall_impl; last eassumption.
      move=> ? /der_mon. apply. by lia.
    - apply: target_S. by eassumption.
Qed.

(* every compound derivation can be decomposed *)
Lemma der_hsc {Gamma t n} : der Gamma n t -> hsc Gamma t.
Proof.
  elim: n Gamma t.
    by move=> > /der_0E.
  move=> n IH Gamma t /derE.
  move=> [ζ [s [k [-> [? [+ +]]]]]].
  have : hsc Gamma (substitute ζ s) by apply: hsc_var.
  move: IH. clear. move: (substitute ζ s) => {}s. clear.
  move=> IH. elim: k s.
    move=> s /= *. by subst t.
  move=> k IHk. case.
    move=> ? /= *. by subst t.
  move=> s1 s2 /=. rewrite ? Forall_norm. 
  move=> /hsc_arr + [/IH +]. move=> + H. by move=> /(_ H){H} /IHk.
Qed.

(* number of nodes in the syntax tree of a formula *)
Fixpoint size s := 
  match s with
  | var _ => 1
  | arr s t => S (size s + size t)
  end.

Lemma encode_word_last {a v} : encode_word (v ++ [a]) = arr (if a then b2 else b3) (encode_word v).
Proof. 
  rewrite /encode_word. move: (bullet) => r. elim: v r.
    move=> r /=. by case: a.
  move=> b A IH r /=. case: b; by rewrite IH.
Qed.

Lemma encode_word_app {v x} : encode_word (v ++ x) = append_word (encode_word v) x.
Proof.
  elim: x v.
    move=> v. by rewrite app_nil_r.
  move=> a x IH v. 
  rewrite -/(app [a] _) ? app_assoc IH encode_word_last.
  move=> /=. by case: a.
Qed.

(* unifiable words are equal *)
Lemma unify_words {v w ζ} : substitute ζ (encode_word v) = substitute ζ (encode_word w) -> v = w.
Proof.
  move: v w. elim /list_last_ind.
    elim /list_last_ind.
      done.
    move=> b w _. rewrite encode_word_last. case: b => /=.
      move /(f_equal size) => /=. by lia.
    move /(f_equal size) => /=. by lia.
  move=> a v IH. elim /list_last_ind.
    rewrite encode_word_last. case: a => /=.
      move /(f_equal size) => /=. by lia.
    move /(f_equal size) => /=. by lia.
  move=> b w _. rewrite ? encode_word_last.
  case: a; case: b; move=> /=; case.
  - by move /IH => ->.
  - move /(f_equal size) => /=. by lia.
  - move /(f_equal size) => /=. by lia.
  - by move /IH => ->.
Qed.

Lemma substitute_combine {ζ ξ r v x} :
  ζ 0 = ξ 0 -> 
  substitute ζ r = substitute ξ (encode_word v) -> 
  substitute ζ (append_word r x) = substitute ξ (encode_word (v ++ x)).
Proof.
  move=> ?. elim: x v r.
    move=> ? /=. by rewrite app_nil_r.
  move=> a x IH v r /=.
  have -> : v ++ a :: x = v ++ [a] ++ x by done.
  rewrite app_assoc. move=> ?. case: a.
  - apply: IH. rewrite encode_word_last. move=> /=. by congruence.
  - apply: IH. rewrite encode_word_last. move=> /=. by congruence.
Qed.

From Undecidability Require Import Problems.PCP.

Lemma tau1_lastP {x y: list bool} {A} : tau1 (A ++ [x / y]) = tau1 A ++ x.
Proof.
  elim: A.
    move=> /=. by rewrite app_nil_r.
  move=> [a b] A /= ->.
  by rewrite app_assoc.
Qed.

Lemma tau2_lastP {x y: list bool} {A} : tau2 (A ++ [x / y]) = tau2 A ++ y.
Proof.
  elim: A.
  move=> /=. by rewrite app_nil_r.
  move=> [a b] A /= ->.
  by rewrite app_assoc.
Qed.

(* derivability of an instance of a → b → a *)
Definition adequate v w P n := 
  exists p q, der (Γ v w P) n (arr p (arr q p)).

(* derivability of (v ++ v₁ ++...++ vₙ, w ++ w₁ ++...++ wₙ) *)
Definition solving (v w: list bool) P n := 
  exists A, 
    (incl A ((v, w) :: P)) /\ 
    exists ζ, der (Γ v w P) n 
      (substitute ζ (encode_pair 
        (encode_word (v ++ tau1 A))
        (encode_word (w ++ tau2 A)))).

Lemma adequate_step {v w P n} : adequate v w P (S n) -> adequate v w P n \/ solving v w P n.
Proof.
  move=> [p [q /derE]] => [[ζ [s [k [_]]]]].
  rewrite {1}/Γ /In -/(In _ _). case. case; last case.
  (* case ⟨ a, a ⟩ *)
  {
    move=> ?. subst s. case: k.
      move=> [_] /=. case=> -> ->.
      move=> /(f_equal size) /=. by lia.
    move=> k /=. rewrite ? Forall_norm. move=> [[? _]] _. left.
    eexists. eexists. by eassumption.
  }
  (* case ⟨ v, w ⟩ → a → b → a *)
  {
    move=> ?. subst s. case: k.
      move=> [_] /=. case=> <- _.
      case=> _ /(f_equal size) /=. by lia.
    move=> k /=. rewrite ? Forall_norm. move=> [[? _]] _. right.
    exists []. constructor.
      done.
    eexists. rewrite /flat_map ? app_nil_r => /=. by eassumption.
  }
  (* case ⟨ va, wb ⟩ → ⟨ a, b ⟩ *)
  {
    move /in_map_iff => [[x y] [<- _]] /=. case: k; last case.
    - move=> [_] /=.
      case=> <- _. case=> _ _ _ /(f_equal size) /=. by lia.
    - move=> [_] /=. case=> <- _. move=> /(f_equal size) /=. by lia.
    - move=> k /=. rewrite ? Forall_norm. move=> [[_ [? _]] _].
      left. eexists. eexists. by eassumption. 
  }
Qed.

Lemma solving_step {v w P n} : solving v w P (S n) -> adequate v w P n \/ solving v w P n \/ BMPCP ((v, w), P).
Proof.
  move=> [A [HA [ξ /derE]]]. move=> [ζ [s [k [_]]]].
  rewrite {1}/Γ /In -/(In _ _). case. case; last case.
  (* case ⟨ a, a ⟩ *)
  {
    move=> ?. subst s. case: k.
      move=> /= [_]. case=> _ _ _ -> /unify_words HA2 _ _ _.
      right. right. eexists. by constructor; eassumption.
    move=> k /=. rewrite ? Forall_norm. move => [[?]] *.
    left. eexists. eexists. by eassumption.
  }
  (* case ⟨ v, w ⟩ → a → b → a *)
  {
    move=> ?. subst s. case: k.
      move=> /= [_]. case=> <- _ /(f_equal size) /=. by lia.
    move=> k /=. rewrite ? Forall_norm. move=> [[?]] *.
    right. left. exists [].
    constructor.
      done.
    eexists. move=> /=. rewrite ? app_nil_r. by eassumption. 
  }
  (* case ⟨ va, wb ⟩ → ⟨ a, b ⟩ *)
  {
    move /in_map_iff => [[x y]]. move=> [<- ?] /=. case: k; last case.
    (* k = 0 *)
    - move=> [_] /=. case=> -> _ /(f_equal size) /=. by lia.
    (* k = 1 *)
    - move=> /=. rewrite ? Forall_norm. 
      move=> [H1]. case=> H2. move: H1. rewrite H2.
      rewrite - ? /(substitute ζ (var _)).
      move=> + _ _ /(substitute_combine H2 (x := x)) Hx.
      move=> + /(substitute_combine H2 (x := y)) Hy _ _ _.
      rewrite Hx Hy => HD.
      right. left.
      exists (A ++ [(x, y)]). constructor.
        move: HA. rewrite /incl - ? Forall_forall ? Forall_norm.
        move=> ?. by constructor.
      exists ξ => /=. by rewrite tau1_lastP tau2_lastP ? app_assoc.
    (* k = 2 *)
    - move=> k /=. rewrite ? Forall_norm. move=> [[_ [?]]] *.
      left. eexists. eexists. by eassumption.
  }
Qed.

Lemma adequate0E {v w P} : not (adequate v w P 0).
Proof. by move=> [? [?]] /der_0E. Qed.

Lemma solving0E {v w P} : not (solving v w P 0).
Proof. by move=> [? [? [?]]] /der_0E. Qed.

(* if ((v, w), P) is adequate, then BMPCP is solvable *)
Lemma complete_adequacy {v w P n}: adequate v w P n -> BMPCP ((v, w), P).
Proof.
  apply: (@proj1 _ (solving v w P n -> BMPCP ((v, w), P))).
  elim: n.
    constructor.
      by move /adequate0E.
    by move /solving0E.
  move=> n [IH1 IH2]. constructor.
    by case /adequate_step.
  by case /solving_step; last case.
Qed.

(* if a → b → a is derivable, then BMPCP is solvable *)
Lemma completeness {v w P} : hsc (Γ v w P) a_b_a -> BMPCP ((v, w), P).
Proof.
  move /hsc_der => [n ?].
  apply: complete_adequacy.
  eexists. eexists. by eassumption.
Qed.  

Lemma transparent_encode_pair {ζ s t} : ζ 0 = var 0 -> 
  substitute ζ (encode_pair s t) = encode_pair (substitute ζ s) (substitute ζ t).
Proof. by move=> /= ->. Qed.

Lemma transparent_append_word {ζ s v} : ζ 0 = var 0 -> 
  substitute ζ (append_word s v) = append_word (substitute ζ s) v.
Proof. 
  move=> Hζ. elim: v s.
    done.
  move=> a v IH s /=. case: a.
    rewrite /b2 /bullet IH => /=. by rewrite Hζ.
  rewrite /b3 /bullet IH => /=. by rewrite Hζ.
Qed.

Lemma substitute_arrP {ζ s t} : substitute ζ (arr s t) = arr (substitute ζ s) (substitute ζ t).
Proof. done. Qed. 

(* key inductive argument for the soundness lemma *)
Lemma soundness_ind {v w P x y A} : 
  incl A ((v, w) :: P) -> 
  x ++ tau1 A = y ++ tau2 A -> 
  hsc (Γ v w P) (encode_pair (encode_word x) (encode_word y)).
Proof.
  elim: A x y.
    move=> x y _ /=. rewrite ? app_nil_r => <-.
    pose ζ i := if i is 1 then encode_word x else var i.
    have -> : encode_pair (encode_word x) (encode_word x) = 
      substitute ζ (encode_pair (var 1) (var 1)) by done.
    apply: hsc_var.
    rewrite /Γ /In. by left.
  move=> [a b] A IH x y /incl_consP [? ?].
  rewrite /tau1 -/tau1 /tau2 -/tau2 ? app_assoc.
  move /IH => /(_ ltac:(assumption)) ?.
  apply: hsc_arr; last eassumption.
  rewrite ? encode_word_app.
  pose ζ i := if i is 2 then encode_word x else if i is 3 then encode_word y else var i.
  have -> : encode_word x = substitute ζ (var 2) by done.
  have -> : encode_word y = substitute ζ (var 3) by done.
  rewrite - ? transparent_append_word; try done.
  rewrite - ? transparent_encode_pair; try done.
  rewrite - substitute_arrP.
  apply: hsc_var. rewrite /Γ.
  right. right. rewrite in_map_iff. 
  exists (a, b). by constructor.
Qed.

Lemma soundness {v w P} : BMPCP ((v, w), P) -> hsc (Γ v w P) a_b_a.
Proof.
  move=> [A [/soundness_ind + H]] => /(_ _ _ H){H} ?.
  apply: hsc_arr; last eassumption.
  pose ζ i := var i.
  have Hζ: forall s, s = substitute ζ s.
    elim.
      done.
    by move=> ? {1}-> ? {1}->.
  rewrite (Hζ (arr _ _)).
  apply: hsc_var. rewrite /Γ. right. by left.
Qed.

(* Reduction from BMPCP to LPB and undecidability of LPB *)

From Undecidability Require Import Problems.Reduction.

Theorem BMPCP_to_LPB : BMPCP ⪯ LPB.
Proof.
  exists (fun '((v, w), P) => exist _ (Γ v w P) Γ_allowed).
  intros [[v w] P]. constructor.
    exact soundness.
  exact completeness.
Qed.

Check BMPCP_to_LPB.
(* Print Assumptions BMPCP_to_LPB. *)

From Undecidability Require Import Problems.TM.
From Undecidability.PCP Require TM_SRH SRH_SR SR_MPCP MPCP_BMPCP.

Theorem LPB_undec : Halt ⪯ LPB.
Proof.
  apply (reduces_transitive TM_SRH.Halt_SRH).
  apply (reduces_transitive SRH_SR.reduction).
  apply (reduces_transitive SR_MPCP.reduction).
  apply (reduces_transitive MPCP_BMPCP.MPCP_to_BMPCP).
  exact BMPCP_to_LPB.
Qed.

Check LPB_undec.
(* Print Assumptions LPB_undec. *)
