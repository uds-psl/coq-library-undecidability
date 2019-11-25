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

From Undecidability Require Import Problems.HSC.

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

Notation "⟨ s , t ⟩" := (encode_pair s t).
Notation "⟦ v ⟧" := (encode_word v).
Notation "s → t" := (arr s t) (at level 50).

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


(*
  Proof that there is a fixed Gamma (ΓPCP) with undecidable provability.
*)

(* fixed type environment encoding PCP *)
Definition ΓPCP :=
  [
    (* ((Q, P), (x, x)) *)
    encode_pair (var 1) (encode_pair (var 2) (var 2));
    (* ((P, P), ((x, v'), (y, w'))) → ((((v', w'), Q), P), ((x, •), (y, •))) *)
    arr 
      (encode_pair (encode_pair (var 4) (var 4)) (encode_pair (encode_pair (var 5) (var 1)) (encode_pair (var 6) (var 2))))
      (encode_pair 
        (encode_pair (encode_pair (encode_pair (var 1) (var 2)) (var 3)) (var 4)) 
        (encode_pair (encode_pair (var 5) bullet) (encode_pair (var 6) bullet)));
    (* ((Q, P), (x, y)) → ((((v', w'), Q), P), (x, y)) *)
    arr 
      (encode_pair (encode_pair (var 2) (var 3)) (var 4))
      (encode_pair (encode_pair (encode_pair (var 1) (var 2)) (var 3)) (var 4));
    (* ((Q, P), ((x, a), v'), y) → ((Q, P), ((x, (a, v')), y) *)
    arr 
      (encode_pair (var 1) (encode_pair (encode_pair (encode_pair (var 2) (var 3)) (var 4)) (var 5)))
      (encode_pair (var 1) (encode_pair (encode_pair (var 2) (encode_pair (var 3) (var 4))) (var 5)));
    (* ((Q, P), (x, ((y, a), w')) → ((Q, P), (x, (y, (a, w'))) *)
    arr 
      (encode_pair (var 1) (encode_pair (var 5) (encode_pair (encode_pair (var 2) (var 3)) (var 4))))
      (encode_pair (var 1) (encode_pair (var 5) (encode_pair (var 2) (encode_pair (var 3) (var 4)))))
  ].


(* not ΓPCP ⊢ r → r → r *)
Lemma not_ΓPCP_rrr n r : not (der ΓPCP n (arr r (arr r r))).
Proof.
  elim: n r.
    by move=> ? /der_0E.
  move=> n IH r /derE => [[ζ [s [k [_ [+ [+]]]]]]].
  rewrite /ΓPCP /In -/ΓPCP. case; last case; last case; last case; last case; last done.
  all: move=> <-.
  case: k => [|k] /=.
    move=> _. case=> <- _. move /(f_equal size) => /=. by lia.
  rewrite Forall_norm. by move=> [/IH].
  all: case: k => [|k] /=.
  1,3,5,7: by (move=> _; case=> _ <-; move /(f_equal size) => /=; by lia).
  all: case: k => [|k] /=.
  1,3,5,7: by (move=> _; case=> <- _; move /(f_equal size) => /=; by lia).
  all: rewrite ? Forall_norm.
  all: by move=> [_ [/IH]].
Qed.

Definition encode_bool b := if b then b2 else b3.

Fixpoint encode_list {X: Type} (encode_X: X -> formula) (A: list X) : formula :=
  match A with
  | [] => bullet
  | a :: A => encode_pair (encode_X a) (encode_list encode_X A)
  end.

Fixpoint encode_word' (s: formula) (v: list bool) :=
  match v with
  | [] => s
  | a :: v => encode_word' (encode_pair s (if a then b2 else b3)) v
  end.

Definition encode_word_pair '(x, y) := encode_pair (encode_list encode_bool x) (encode_list encode_bool y).

(* formula encoding the given PCP instance *)
Definition PCPf P x y := 
  encode_pair 
    (encode_pair (encode_list encode_word_pair P) (encode_list encode_word_pair P)) 
    (encode_pair (encode_pair (encode_word' bullet x) bullet) (encode_pair (encode_word' bullet y) bullet)).

Definition PCPf' Q P s t := 
    encode_pair 
      (encode_pair (encode_list encode_word_pair Q) (encode_list encode_word_pair P)) 
      (encode_pair s t).

Lemma encode_word'_last {x a} : encode_word' bullet (x ++ [a]) = encode_pair (encode_word' bullet x) (encode_bool a).
Proof.
  move: (bullet) => s.
  elim: x s.
    done.
  by move=> b x IH s /=.
Qed.

Lemma hscI {Gamma ζ s t}  : In s Gamma -> t = substitute ζ s -> hsc Gamma t.
Proof. by move=> /hsc_var + ->. Qed.


Lemma ΓPCP_assoc_x {P x r v} : 
  hsc ΓPCP (PCPf' P P 
    (encode_pair (encode_word' bullet (x ++ v)) bullet) r) ->
  hsc ΓPCP (PCPf' P P 
    (encode_pair (encode_word' bullet x) (encode_list encode_bool v)) r).
Proof.
  elim: v x.
    move=> ?. by rewrite app_nil_r.
  move=> a v IH x. rewrite -/(app [a] _) app_assoc. move /IH.
  rewrite encode_word'_last.
  move /(hsc_arr _ _ _ _). apply.
  evar (ζ : nat -> formula).
  instantiate (ζ := fun x => match x with | 0 => _ | 1 => _ | 2 => _ | 3 => _| 4 => _ | _ => _ end).
  apply: (hscI (ζ := ζ)).
    rewrite /ΓPCP. do 3 right. left. by reflexivity.
  by rewrite /ζ substitute_arrP /PCPf' ? transparent_encode_pair.
Qed.


Lemma ΓPCP_assoc_y {P r y w} : 
  hsc ΓPCP (PCPf' P P r 
    (encode_pair (encode_word' bullet (y ++ w)) bullet)) ->
  hsc ΓPCP (PCPf' P P r
    (encode_pair (encode_word' bullet y) (encode_list encode_bool w))).
Proof.
  elim: w y.
    move=> ?. by rewrite app_nil_r.
  move=> a w IH y. rewrite -/(app [a] _) app_assoc. move /IH.
  rewrite encode_word'_last.
  move /(hsc_arr _ _ _ _). apply.
  evar (ζ : nat -> formula).
  instantiate (ζ := fun x => match x with | 0 => _ | 1 => _ | 2 => _ | 3 => _ | 4 => _ | _ => _ end).
  apply: (hscI (ζ := ζ)).
    rewrite /ΓPCP. do 4 right. left. by reflexivity.
  by rewrite /ζ substitute_arrP /PCPf' ? transparent_encode_pair.
Qed.


Lemma ΓPCP_saturate {Q R P s t} : 
  P = R ++ Q ->
  hsc ΓPCP (PCPf' Q P s t) ->
  hsc ΓPCP (PCPf' P P s t).
Proof.
  elim /list_last_ind : R Q P.
    by move=> Q P ->.
  move=> vw R IH Q P. rewrite -app_assoc. move=> ->.
  move=> ?. have : hsc ΓPCP (PCPf' ([vw] ++ Q) (R ++ ([vw] ++ Q)) s t).
    apply: hsc_arr; last eassumption.
    evar (ζ : nat -> formula).
    instantiate (ζ := fun x => match x with | 0 => _ | 1 => _ | 2 => _ | 3 => _ | _ => _ end).
    apply: (hscI (ζ := ζ)).
      rewrite /ΓPCP. do 2 right. left. by reflexivity.
    by rewrite /ζ substitute_arrP /PCPf' ? transparent_encode_pair.
  move /IH. by apply.
Qed.


Lemma ΓPCP_step {P x y v w} : 
  In (v, w) P ->
  hsc ΓPCP (PCPf' P P 
    (encode_pair (encode_word' bullet x) (encode_list encode_bool v)) 
    (encode_pair (encode_word' bullet y) (encode_list encode_bool w))) ->
  hsc ΓPCP (PCPf P x y).
Proof.
  move /(@in_split _ _) => [R [Q ?]] ?.
  have : hsc ΓPCP (PCPf' ((v, w) :: Q) P 
    (encode_pair (encode_word' bullet x) bullet)
    (encode_pair (encode_word' bullet y) bullet)).
    apply: hsc_arr; last eassumption.
    evar (ζ : nat -> formula).
    instantiate (ζ := fun x => match x with | 0 => _ | 1 => _ | 2 => _ | 3 => _ | 4 => _ | 5 => _ | _ => _ end).
    apply: (hscI (ζ := ζ)).
      rewrite /ΓPCP. do 1 right. left. by reflexivity.
    by rewrite /ζ substitute_arrP /PCPf' ? transparent_encode_pair.
  move /ΓPCP_saturate. apply. by eassumption.
Qed.


Lemma ΓPCP_soundness_ind {v w P A} : 
  incl A ((v, w) :: P) -> 
  hsc ΓPCP (PCPf ((v, w) :: P) (v ++ (tau1 A)) (w ++ (tau2 A))) ->
  hsc ΓPCP (PCPf ((v, w) :: P) v w).
Proof.
  elim /list_last_ind : A.
    move=> _ /=. by rewrite ? app_nil_r.
  move=> [x y] A IH. rewrite /incl - Forall_forall ? Forall_norm.
  rewrite Forall_forall -/(incl _ _). move=> [/IH].
  rewrite tau1_lastP tau2_lastP ? app_assoc.
  move=> + ? ?; apply.
  apply: ΓPCP_step; first by eassumption.
  apply: ΓPCP_assoc_x. apply: ΓPCP_assoc_y.
  by assumption.
Qed.

(* if BMPCP has a solution, then the formula (PCPf ((v, w) :: P) v w) is derivable from ΓPCP *)
Lemma ΓPCP_soundness {v w P} : BMPCP ((v, w), P) -> hsc ΓPCP (PCPf ((v, w) :: P) v w).
Proof.
  move=> [A [/ΓPCP_soundness_ind]]. move=> + H.
  rewrite {}H. apply.
  evar (ζ : nat -> formula).
  instantiate (ζ := fun x => match x with | 0 => _ | 1 => _ | _ => _ end).
  apply: (hscI (ζ := ζ)). by left.
  by rewrite /ζ /PCPf transparent_encode_pair.
Qed.

Lemma encode_bool_injective {a b} : encode_bool a = encode_bool b -> a = b.
Proof. case: a b; by case. Qed.

Lemma encode_word'_injective {x y} : encode_word' bullet x = encode_word' bullet y -> x = y.
Proof.
  move: x y.
  elim /list_last_ind => [|a x IHx].
  all: elim /list_last_ind => [|b y IHy].
  all: rewrite ? encode_word'_last.
  all: try done.
  case. by move /IHx => <- /encode_bool_injective <-.
Qed.

Lemma encode_list_injective {x y} : encode_list encode_bool x = encode_list encode_bool y -> x = y.
Proof. 
  elim: x y=> [|a x IH]; case=> //=.
  move=> b y. case.
  by move /encode_bool_injective => <- /IH <-.
Qed.

Lemma substitute_pairP {ζ s t s' t'} : (substitute ζ (encode_pair s t) = encode_pair s' t') <-> ζ 0 = bullet /\ substitute ζ s = s' /\ substitute ζ t = t'.
Proof.
  constructor.
    by case.
  by move=> [+ [+ +]] /= => -> -> ->.
Qed.


Lemma ΓPCP_completeness_ind {Q P x y v w n} : incl Q P -> 
  der ΓPCP n (PCPf' Q P 
    (encode_pair (encode_word' bullet x) (encode_list encode_bool v))
    (encode_pair (encode_word' bullet y) (encode_list encode_bool w))) -> 
  exists A, incl A P /\ x ++ v ++ tau1 A = y ++ w ++ tau2 A.
Proof.
  elim: n Q x y v w.
    by move=> > _ /der_0E.
  move=> n IH Q x y v w HQ /derE.
  move=> [ζ [s [k [_ [+ [+]]]]]].
  have Hu (r) : r = arr r (arr r r) -> False.
    move /(f_equal size) => /=. by lia.
  rewrite /ΓPCP /In -/ΓPCP. case; last case; last case; last case; last case; last done.
  all: move=> <-.
  case: k=> [|k] /=.
    move=> _. case. do 7 (move=> _). move=> ->.
    case=> /encode_word'_injective + /encode_list_injective.
    move=> -> ->. do 6 (move=> _). by exists [].
  rewrite ? Forall_norm. by move=> [/not_ΓPCP_rrr].
  all: case: k=> [|k].
  1,3,5,7: move=> _ /=; case=> <- *; exfalso; apply: Hu; by eassumption.
  all: case: k=> [|k].
  2,4,6,8: move=> /=; rewrite ? Forall_norm; by move=> [_ [/not_ΓPCP_rrr]].
  all: rewrite substitute_arrP /arguments ? Forall_norm /target.
  all: move=> Hder.
  all: rewrite ? substitute_pairP.
  (* step case *)
  {
    move=> [H0] [[_ [H123 H4]]] [_] [[_ [H5 Hv]]] [_ [H6 Hw]].
    move: H123 HQ. case: Q.
      done.
    move=> [v' w'] Q. rewrite /encode_list -/encode_list /encode_word_pair -/encode_word_pair.
    rewrite ? substitute_pairP.
    move=> [_ [[_ [H1 H2]] H3]].
    move: Hder. rewrite ? transparent_encode_pair //.
    rewrite H1 H2 H4 H5 H6. move /IH. move /(_ ltac:(done)).
    move=> [A [HAP HxyA]].
    move /(_ (v', w')). move /(_ ltac:(by left)) => ?.
    move: Hv Hw. case: v. case: w.
    move=> _ _.
    exists ((v', w') :: A). constructor.
      rewrite /incl - Forall_forall ? Forall_norm Forall_forall. by constructor.
    by assumption.
    all: by move=> ? ? /=; rewrite H0.
  }
  (* cons case *)
  {
    move=> [H0] [[_ [H12 H3]]] H4.
    move: H12 HQ. case: Q.
      done.
    move=> ? Q. rewrite /encode_list -/encode_list ? substitute_pairP. move=> [_ [_ H2]].
    rewrite /incl -Forall_forall ? Forall_norm Forall_forall.
    move=> [_ HQ].
    move: Hder. rewrite ? transparent_encode_pair => //.
    rewrite H2 H3 H4. move /IH.
    by apply.
  }
  (* assoc x case *)
  {
    move=> [H0] [H1] [_] [[_ [H2]]] H34 H5.
    move: H34. case: v.
      done.
    move=> a v. rewrite /encode_list -/encode_list substitute_pairP.
    move=> [_ [H3 H4]].
    move: Hder. rewrite ? transparent_encode_pair => //.
    rewrite H1 H2 H3 H4 H5 -encode_word'_last. move /IH.
    rewrite -/(app [a] v). move /(_ ltac:(done)) => [A [?]].
    rewrite - ? app_assoc => ?.
    by exists A.
  }
  (* assoc y case *)
  {
    move=> [H0] [H1] [_] [H5] [_ [H2 H34]].
    move: H34. case: w.
      done.
    move=> a w. rewrite /encode_list -/encode_list substitute_pairP.
    move=> [_ [H3 H4]].
    move: Hder. rewrite ? transparent_encode_pair => //.
    rewrite H1 H2 H3 H4 H5 -encode_word'_last. move /IH.
    rewrite -/(app [a] w). move /(_ ltac:(done)) => [A [?]].
    rewrite - ? app_assoc => ?.
    by exists A.
  }
Qed.

(* if the formula (PCPf ((v, w) :: P) v w) is derivable from ΓPCP, then BMPCP has a solution *)
Lemma ΓPCP_completeness {v w P} : hsc ΓPCP (PCPf ((v, w) :: P) v w) -> BMPCP ((v, w), P).
Proof.
  move /hsc_der => [n].
  have -> : PCPf (v / w :: P) v w = 
    PCPf' (v / w :: P) (v / w :: P) 
      (encode_pair (encode_word' bullet v) (encode_list encode_bool []))
      (encode_pair (encode_word' bullet w) (encode_list encode_bool [])) by done.
  move /ΓPCP_completeness_ind. by apply.
Qed.

(* Reduction from BMPCP to HSC_AX and undecidability of HSC_AX *)

From Undecidability Require Import Problems.Reduction.

Theorem BMPCP_to_HSC_AX : BMPCP ⪯ HSC_AX.
Proof.
  exists (fun '((v, w), P) => exist _ (Γ v w P) Γ_allowed).
  intros [[v w] P]. constructor.
    exact soundness.
  exact completeness.
Qed.

Check BMPCP_to_HSC_AX.
(* Print Assumptions BMPCP_to_HSC_AX. *)

From Undecidability Require Import Problems.TM.
From Undecidability.PCP Require TM_SRH SRH_SR SR_MPCP MPCP_BMPCP.

Theorem HSC_AX_undec : Halt ⪯ HSC_AX.
Proof.
  apply (reduces_transitive TM_SRH.Halt_SRH).
  apply (reduces_transitive SRH_SR.reduction).
  apply (reduces_transitive SR_MPCP.reduction).
  apply (reduces_transitive MPCP_BMPCP.MPCP_to_BMPCP).
  exact BMPCP_to_HSC_AX.
Qed.

Check HSC_AX_undec.
(*Print Assumptions HSC_AX_undec.*)

(* Reduction from BMPCP to HSC_PRV and undecidability of HSC_PRV *)

From Undecidability Require Import Problems.Reduction.

Theorem BMPCP_to_HSC_PRV : BMPCP ⪯ HSC_PRV ΓPCP.
Proof.
  exists (fun '((v, w), P) => (PCPf ((v, w) :: P) v w)).
  intros [[v w] P]. constructor.
    exact ΓPCP_soundness.
  exact ΓPCP_completeness.
Qed.

Check BMPCP_to_HSC_PRV.
(* Print Assumptions BMPCP_to_HSC_PRV. *)

From Undecidability Require Import Problems.TM.
From Undecidability.PCP Require TM_SRH SRH_SR SR_MPCP MPCP_BMPCP.

Theorem HSC_PRV_undec : Halt ⪯ HSC_PRV ΓPCP.
Proof.
  apply (reduces_transitive TM_SRH.Halt_SRH).
  apply (reduces_transitive SRH_SR.reduction).
  apply (reduces_transitive SR_MPCP.reduction).
  apply (reduces_transitive MPCP_BMPCP.MPCP_to_BMPCP).
  exact BMPCP_to_HSC_PRV.
Qed.

Check HSC_PRV_undec.
(*Print Assumptions HSC_PRV_undec.*)
