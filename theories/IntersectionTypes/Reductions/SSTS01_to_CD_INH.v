(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Reduction from:
    Simple Semi-Thue System 01 Rewriting (SSTS01)
  to:
    Intersection Type Inhabitation (CD_INH)
*)

Require Import Undecidability.IntersectionTypes.CD Undecidability.IntersectionTypes.Util.CD_facts.
Require Undecidability.L.L.
Require Import Undecidability.StringRewriting.SSTS.
Require Import Undecidability.LambdaCalculus.Util.term_facts.

Require Import Relations List PeanoNat Lia.
Import ListNotations.

Import L (term, var, app, lam).

Require Import ssreflect ssrfun.

Set Default Goal Selector "!".

Unset Implicit Arguments.

Lemma map_nth_seq {X : Type} (l : list X) d : 
  map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  elim: l; first done.
  move=> ? ? IH /=. by rewrite -seq_shift map_map IH.
Qed.

Lemma map_nth' {A B : Type} {f : A -> B} {l : list A} {d : B} {n : nat} (d' : A) :
  n < length l -> nth n (map f l) d = f (nth n l d').
Proof.
  move=> ?. rewrite -[RHS]map_nth. apply: nth_indep. by rewrite length_map.
Qed.

Lemma Forall_In_impl {X : Type} {P Q : X -> Prop} {l : list X} :
  (forall x, In x l -> P x -> Q x) -> Forall P l -> Forall Q l.
Proof. move=> ? /Forall_forall ?. apply /Forall_forall. by auto with nocore. Qed.

Lemma step_spec (rs : Ssts) a b a' b' i v : In ((a, b), (a', b')) rs ->
  nth_error v i = Some a -> nth_error v (S i) = Some b ->
  step rs v (map (fun j => if Nat.eqb j i then a' else if Nat.eqb j (S i) then b' else nth j v 0) (seq 0 (length v))).
Proof.
  move=> /step_intro H. elim: i v.
  { move=> [|? [|? v]] /=; [done|done|].
    move=> [->] [->]. have := H [] v.
    by rewrite -!seq_shift !map_map /= map_nth_seq. }
  move=> i IH [|? v] /=; first done.
  move=> /IH /[apply]. rewrite -!seq_shift !map_map /=.
  move: (map _ _) => ? [] > /step_intro H'.
  by apply: (H' (_ :: _) _).
Qed.

Lemma step_length_eq (rs : Ssts) v w : step rs v w -> length v = length w.
Proof. case => > _. by rewrite !length_app. Qed.

#[local] Notation bullet := (atom 0).
#[local] Notation star := (atom 1).
(*indicates second symbol*)
#[local] Notation hash := (atom 2).
(*indicates first symbol*)
#[local] Notation dollar := (atom 3).
(*indicates very first split, used once*)
#[local] Notation triangle := (atom 4).
#[local] Notation isl := (atom 5).
#[local] Notation isr := (atom 6).

Section Argument.

(*encodes elements of the alphabet including 0 and 1*)
Definition symbol (a : nat) := atom (7 + a).

Definition arr' phi t :=
  match phi with
  | [] => t
  | s::phi => arr s phi t
  end.

#[local] Arguments arr' /.

Definition mk_ty phi :=
  match phi with
  | [] => (atom 0, [])
  | s::phi => (s, phi)
  end.

#[local] Arguments mk_ty /.

Definition s_init : ty :=
  mk_ty [arr' [hash; dollar] triangle].

Definition s_star : ty := mk_ty [
  arr' [arr' [bullet] star] star; 
  arr' [arr' [isr] star] hash;
  arr' [arr' [isl] hash; arr' [bullet] dollar] dollar].

Definition s_0 : ty := mk_ty
  [arr' [symbol 0] star; arr' [symbol 0] hash; arr' [symbol 1] dollar].

Definition s_1 : ty := mk_ty [symbol 1].

#[local] Notation rule := ((nat * nat) * (nat * nat))%type.

Context (rs : list rule).

Definition symbols :=
  (flat_map (fun '((a,b),(c,d)) => [a; b; c; d]) rs) ++ [0; 1].

Definition s_id_rules : list sty :=
  map (fun (a : nat) => (arr' [bullet] (arr' [symbol a] (symbol a)))) symbols.

Definition s_rule (r : rule) : ty :=
  match r with
  | ((x,y),(x',y')) => mk_ty (
      (arr' [isl] (arr' [symbol x'] (symbol x))) ::
      (arr' [isr] (arr' [symbol y'] (symbol y))) ::
      s_id_rules)
  end.

Definition s_pos (i j : nat) : ty := if Nat.eqb i j then mk_ty [isl] else (if Nat.eqb i (S j) then mk_ty [isr] else mk_ty [bullet]).

(*used for initialization, expansion, and termination*)
Definition Γ_init : list ty := [s_init; s_star; s_0; s_1].

Definition Γ_step : list ty := map s_rule rs.

(*information on 'neighboring' environments*)
Definition Γ_lr (bound : nat) (i : nat) : list ty := map (fun j => s_pos i j) (seq 0 bound).

(*collection of all the above type environments*)
Definition Γ_all (bound i : nat) :=
  Γ_lr bound i ++ (Γ_init ++ Γ_step).

Inductive Γ_all_spec (bound i x : nat) t : Prop :=
  | Γ_all_lr_r : t = isr -> (forall i', nth_error (Γ_all bound i') x = Some (s_pos i' x)) -> i = S x -> x < bound -> Γ_all_spec bound i x t
  | Γ_all_lr_l : t = isl -> (forall i', nth_error (Γ_all bound i') x = Some (s_pos i' x)) -> i = x -> x < bound -> Γ_all_spec bound i x t
  | Γ_all_lr_bullet : t = bullet -> (forall i', nth_error (Γ_all bound i') x = Some (s_pos i' x)) -> i <> x -> i <> S x -> x < bound -> Γ_all_spec bound i x t
  | Γ_all_init_init : t = (arr' [hash; dollar] triangle) -> (forall i', nth_error (Γ_all bound i') x = Some s_init) -> Γ_all_spec bound i x t
  | Γ_all_init_star_star : t = (arr' [arr' [bullet] star] star) -> (forall i', nth_error (Γ_all bound i') x = Some s_star) -> Γ_all_spec bound i x t
  | Γ_all_init_star_hash : t = (arr' [arr' [isr] star] hash) -> (forall i', nth_error (Γ_all bound i') x = Some s_star) -> Γ_all_spec bound i x t
  | Γ_all_init_star_dollar : t = (arr' [arr' [isl] hash; arr' [bullet] dollar] dollar) -> (forall i', nth_error (Γ_all bound i') x = Some s_star) -> Γ_all_spec bound i x t
  | Γ_all_init_0_star : t = (arr' [symbol 0] star) -> (forall i', nth_error (Γ_all bound i') x = Some s_0) -> Γ_all_spec bound i x t
  | Γ_all_init_0_hash : t = (arr' [symbol 0] hash) -> (forall i', nth_error (Γ_all bound i') x = Some s_0) -> Γ_all_spec bound i x t
  | Γ_all_init_0_dollar : t = (arr' [symbol 1] dollar) -> (forall i', nth_error (Γ_all bound i') x = Some s_0) -> Γ_all_spec bound i x t
  | Γ_all_init_1 : t = (symbol 1) -> (forall i',nth_error (Γ_all bound i') x = Some s_1) -> Γ_all_spec bound i x t
  | Γ_all_step_l a b a' b' : t = (arr' [isl] (arr' [symbol a'] (symbol a))) -> (forall i', nth_error (Γ_all bound i') x = Some (s_rule ((a, b), (a', b')))) -> In ((a, b), (a', b')) rs -> Γ_all_spec bound i x t
  | Γ_all_step_r a b a' b' : t = (arr' [isr] (arr' [symbol b'] (symbol b))) -> (forall i', nth_error (Γ_all bound i') x = Some (s_rule ((a, b), (a', b')))) -> In ((a, b), (a', b')) rs -> Γ_all_spec bound i x t
  | Γ_all_step_e a b a' b' e : t = (arr' [bullet] (arr' [symbol e] (symbol e))) -> (forall i', nth_error (Γ_all bound i') x = Some (s_rule ((a, b), (a', b')))) -> In ((a, b), (a', b')) rs -> In e symbols -> Γ_all_spec bound i x t.

Lemma nth_Γ_common x bound i i' :
  x >= length (Γ_lr bound i) ->
  nth_error (Γ_all bound i') x = nth_error (Γ_all bound i) x.
Proof.
  move=> Hx. rewrite /Γ_all [LHS]nth_error_app2.
  { move: Hx. by rewrite /Γ_lr !length_map !length_seq. }
  rewrite [RHS]nth_error_app2; first done.
  by rewrite /Γ_lr !length_map !length_seq.
Qed.

Lemma In_Γ_allE bound i x s phi t :
  nth_error (Γ_all bound i) x = Some (s, phi) ->
  In t (s::phi) ->
  Γ_all_spec bound i x t.
Proof.
  have [|] : x < length (Γ_lr bound i) \/ x >= length (Γ_lr bound i) by lia.
  { rewrite /Γ_lr length_map length_seq => Hx.
    have H'x : forall i', nth_error (Γ_all bound i') x = Some (s_pos i' x).
    { move=> i'. rewrite /Γ_all nth_error_app1. { by rewrite /Γ_lr length_map length_seq. }
      by rewrite /Γ_lr nth_error_map CD_facts.nth_error_seq. }
    rewrite H'x /s_pos. case Eix: (Nat.eqb i x) => /=.
    { move=> [<- <-]. case; last done. move=> ?. move=> /Nat.eqb_eq in Eix. subst. by apply: Γ_all_lr_l. }
    case E'ix: (Nat.eqb i (S x)).
    { move=> [<- <-]. case; last done. move=> ?. move=> /Nat.eqb_eq in E'ix. subst. by apply: Γ_all_lr_r. }
    move=> [<- <-]. case; last done. move=> <-. move=> /Nat.eqb_neq in Eix. move=> /Nat.eqb_neq in E'ix.
    by apply: Γ_all_lr_bullet. }
  rewrite /Γ_all. move=> /[dup] /nth_error_app2 + /nth_Γ_common.
  rewrite /Γ_all. move=> ->. move: (x - _).
  case. { move=> /= ? [<- <-]. by do 1 (case; [move=> <-; by eauto using Γ_all_spec, erefl with nocore|]). }
  case. { move=> /= ? [<- <-]. by do 3 (case; [move=> <-; by eauto using Γ_all_spec, erefl with nocore|]). }
  case. { move=> /= ? [<- <-]. by do 3 (case; [move=> <-; by eauto using Γ_all_spec, erefl with nocore|]). }
  case. { move=> /= ? [<- <-]. by do 1 (case; [move=> <-; by eauto using Γ_all_spec, erefl with nocore|]). }
  move=> x' /=.
  rewrite /Γ_step nth_error_map. move E: (nth_error rs x') => [[[? ?][? ?]]|]; last done.
  move=> /(@nth_error_In rule) in E.
  move=> ? [<- <-] /=.
  do 2 (case; [move=> <-; by eauto using Γ_all_spec, erefl with nocore|]).
  move=> /in_map_iff [?] [<-]. by eauto using Γ_all_spec, erefl with nocore.
Qed.

(*only s_rule can be used deriving a type with two parameters for a normal form*)
Lemma two_params_rule (bound i: nat) N phi psi (s1 s2 t : sty) :
  neutral normal_form N ->
  type_assignment (Γ_all bound i) N (arr s1 phi (arr s2 psi t)) ->
  (exists x (e : nat), N = var x /\ t = symbol e).
Proof.
  move=> H. elim: H s1 phi s2 psi t.
  { move=> x > /type_assignmentE [] > /In_Γ_allE /[apply].
    move=> [] // > [] *; subst; by eexists _, _. }
  move=> > ? IH ? > /type_assignmentE [] > /IH.
  firstorder done.
Qed.

Lemma nf_hf_atom Gamma N a :
  normal_form N ->
  type_assignment Gamma N (atom a) ->
  neutral normal_form N.
Proof.
  case.
  + by constructor.
  + by move=> > ? /type_assignmentE.
  + by do ? constructor.
  + move=> > /normal_form_app_neutral *. by constructor.
Qed.

(*if triangle is inhabited in (Γ_init ++ Γ_step rs), then hash, dollar is inhabited in (Γ_all rs 0 0)*)
Lemma soundness_init (N : term) :
  neutral normal_form N ->
  type_assignment (Γ_init ++ Γ_step) N triangle ->
  exists (N' : term), neutral normal_form N' /\
  type_assignment (Γ_all 0 0) N' hash /\
  type_assignment (Γ_all 0 1) N' dollar.
Proof.
  case.
  { move=> x /type_assignmentE [>] /(In_Γ_allE 0 0) /[apply]. by case. }
  move=> ? N' []; first last.
  { move=> > /two_params_rule H ??.
    move=> /type_assignmentE [>] /type_assignmentE [>].
    by move=> /(H 0 0) [?] [?] []. }
  move=> ?? /type_assignmentE [>] /type_assignmentE [>] /(In_Γ_allE 0 0) /[apply].
  case=> //.
  move=> [-> ->] ? ? /Forall_cons_iff [? _].
  exists N'. split; last done.
  apply: nf_hf_atom; by eassumption.
Qed.

Lemma Γ_lr_bound_S bound : Γ_lr bound (S bound) = map (fun=> (bullet, [])) (seq 0 bound).
Proof.
  apply: map_ext_in => j /in_seq ?. rewrite /s_pos.
  have /Nat.eqb_neq -> : S bound <> j by lia.
  by have /Nat.eqb_neq -> : S bound <> S j by lia.
Qed.

(*if stars, hash, dollar is inhabited in (Γ_all rs bound [0 .. 1+bound]), then 0 is inhabited in (Γ_all rs bound [0 .. bound'])*)
Lemma soundness_expand (bound : nat) (N : term) :
  neutral normal_form N ->
  Forall (fun Γi => type_assignment Γi N star) (map (Γ_all bound) (seq 1 bound)) ->
  type_assignment (Γ_all bound 0) N hash ->
  type_assignment (Γ_all bound (1+bound)) N dollar ->
  exists bound' N',
    neutral normal_form N' /\
    Forall (fun Γi => type_assignment Γi N' (symbol 0)) (map (Γ_all bound') (seq 0 (1+bound'))).
Proof.
  elim /(Nat.measure_induction _ term_size): N bound.
  move=> ? + bound Hx. case: Hx.
  { move=> ? IH ? /type_assignmentE [>] /In_Γ_allE /[apply]. by case. }
  move=> M N []; first last.
  { move=> > /two_params_rule H ???? /type_assignmentE [>] /type_assignmentE [>].
    by move=> /H [?] [?] []. }
  move=> ? H0N IH IH' /type_assignmentE [>] /type_assignmentE [>].
  move=> /In_Γ_allE /[apply]. case=> //.
  - move=> [-> ->] Hx H1N _.
    move: H0N IH IH' H1N => /normal_form_neutral [].
    { move=> [].
      - move=> ??? /type_assignmentE [>] /In_Γ_allE /[apply]. by case.
      - by move=> > /two_params_rule H ??? /type_assignmentE [>] /H [?] [?] []. }
    move=> [] N' [->] H0N' IH IH' /type_assignmentE H1N'.
    move=> /type_assignmentE [>] /type_assignmentE [>].
    rewrite Hx=> - [<- <-]. case; [done|case;[done|case;[|done]]].
    move=> [<- <-]/type_assignmentE H2N' /Forall_cons_iff [/type_assignmentE H3N' _].
    apply: (IH N' _ (S bound)).
    + move=> /=. lia.
    + by apply: nf_hf_atom; eassumption.
    + move=> /=. constructor.
      { move: H1N'. by rewrite /Γ_all /= -seq_shift map_map. }
      move: IH'. rewrite -!seq_shift !map_map.
      move=> /Forall_map IH'. apply /Forall_map. apply: Forall_impl IH'.
      move=> ? /type_assignmentE [>] /type_assignmentE [>].
      rewrite Hx=> - [<- <-]. case; [|case;[done|by case]].
      move=> [<- <-] /type_assignmentE + _.
      by rewrite /Γ_all /= -seq_shift map_map.
    + move: H2N'. congr type_assignment.
      rewrite /Γ_all /=. congr cons. congr List.app.
      rewrite -seq_shift map_map. apply: map_ext_in => j /in_seq ?. rewrite /s_pos.
      have /Nat.eqb_neq -> : S bound <> j by lia.
      by have /Nat.eqb_neq -> : S bound <> S j by lia.
    + move: H3N'. by rewrite /Γ_all /= -seq_shift map_map.
  - move=> [-> ->] Hx ? _ /type_assignmentE [>] /type_assignmentE [>].
    rewrite Hx=> - [<- <-]. case; [done|case;[done|case;[|done]]].
    move=> [<- <-] ? _.
    exists bound, N. split. { by apply: nf_hf_atom; eassumption. }
    move=> /=. constructor; [done|].
    apply /Forall_forall => ? /[dup] /in_map_iff [?] [<-] ?.
    move: IH' => /Forall_forall /[apply].
    move=> /type_assignmentE [>] /type_assignmentE [>].
    rewrite Hx=> - [<- <-]. case; [|case;[done|by case]].
    by move=> [<- <-].
Qed.

Lemma Forall_nth_const v :
  Forall (fun i => nth i v 0 = 1) (seq 0 (length v)) ->
  v = repeat 1 (length v).
Proof.
  elim: v; first done.
  move=> ? v IH /= /Forall_cons_iff [->].
  by rewrite -seq_shift Forall_map => /IH <-.
Qed.

Lemma s_rule_spec bound x s1 phi s2 psi a N :
  type_assignment (Γ_all bound bound) (var x) (arr s1 phi (arr s2 psi (symbol a))) ->
  normal_form N ->
  type_assignment (Γ_all bound bound) N s1 ->
  (exists r, In r rs /\ (forall i', nth_error (Γ_all bound i') x = Some (s_rule r))) /\
  exists y, N = var y /\ y < bound /\ (forall i', nth_error (Γ_all bound i') y = Some (s_pos i' y)).
Proof.
  move=> /type_assignmentE [>] /In_Γ_allE /[apply] Hx HN Hs1. split.
  { by case: Hx => // *; eexists; split; eassumption. }
  have {}HN : neutral normal_form N.
  { move: HN Hs1 => /normal_form_neutral []; first done.
    move=> [?] [-> ?]. move: Hx.
    by case=> // > [?????] _ _ => [| |_]; subst => /type_assignmentE. }
  case: HN Hs1.
  { move=> y Hy. exists y. split; first done.
    case: Hx Hy => // > [-> ????] _ _ => [| |_].
    all: by move=> /type_assignmentE [>] /In_Γ_allE /[apply] - []. }
  move=> > [].
  { move=> ??. move: Hx.
    case=> // > [-> ????] _ _ => [| |_].
    all: move=> /type_assignmentE [>] /type_assignmentE [>].
    all: by move=> /In_Γ_allE /[apply] - []. }
  move=> > /two_params_rule H ??. move: Hx.
  case=> // > [-> ????] _ _ => [| |_].
  all: move=> /type_assignmentE [>] /type_assignmentE [>].
  all: by move=> /H [?] [?] [].
Qed.

Inductive In_s_rule (t : sty) (a b a' b': nat) : Prop :=
  | In_s_rule_a_a' : t = arr' [isl] (arr' [symbol a'] (symbol a)) -> In_s_rule t a b a' b'
  | In_s_rule_b_b' : t = arr' [isr] (arr' [symbol b'] (symbol b)) -> In_s_rule t a b a' b'
  | In_s_rule_id e : t = arr' [bullet] (arr' [symbol e] (symbol e)) -> In e symbols -> In_s_rule t a b a' b'.

Lemma In_s_rule_spec t a b a' b' :
  let '(s, phi) := s_rule (a, b, (a', b')) in
  In t (s::phi) ->
  In_s_rule t a b a' b'.
Proof.
  move=> /= [|[|/in_map_iff [?] []]].
  all: by eauto using In_s_rule, esym with nocore.
Qed.

(*if [a_0 .. a_bound] is inhabited in (Γ_all bound [0 .. bound], then a_0..a_bound rewrites to 1..1 *)
Lemma soundness_step (bound : nat) (N : term) (v : list nat) :
  neutral normal_form N ->
  length v = bound + 1 ->
  Forall (fun i => type_assignment (Γ_all bound i) N (symbol (nth i v 0))) (seq 0 (bound + 1)) ->
  multi_step rs v (repeat 1 (bound + 1)).
Proof.
  elim /(Nat.measure_induction _ term_size): N v.
  move=> N IH v H0N Hv /[dup] H'v.
  rewrite seq_app /= => /Forall_app [_] /Forall_cons_iff [+ _].
  case: H0N IH H'v.
  { move=> ?? H /type_assignmentE [>] /In_Γ_allE /[apply] - [] // ? Hx.
    rewrite (Forall_nth_const v); rewrite Hv; last by apply: rt_refl.
    apply: Forall_impl H => ? /type_assignmentE [>].
    rewrite Hx=> - [<- <-]. by case; case. }
  move=> ? N1 [].
  { by move=> ???? /type_assignmentE [>] /type_assignmentE [>] /In_Γ_allE /[apply] - []. }
  move=> ? N2 /two_params_rule H HN2 HN1 IH IH'.
  move=> /type_assignmentE [>] /type_assignmentE [>] /[dup] H' /H{H}.
  move=> [?] [?] [? _]. subst.
  move: (H') HN2 => /s_rule_spec /[apply] /[apply].
  move=> [[[[a0 b0][a1 b1]]]] [Hr] Hx [y] [?] [H1y H2y] H'N2 H1N1 H2N1. subst.
  have Ha0 : nth_error v y = Some a0.
  { have : In y (seq 0 (bound + 1)) by apply /in_seq; lia.
    move: IH' => /Forall_forall /[apply].
    move=> /type_assignmentE [>] /type_assignmentE [>] /type_assignmentE [>].
    rewrite Hx=> - [<- <-].
    move=> H'' /type_assignmentE [>].
    rewrite H2y /s_pos Nat.eqb_refl => - [<- <-]. case; last done.
    move=> ?. subst. move: H'' => /In_s_rule_spec [] //.
    move=> [] *. subst. apply: nth_error_nth'. lia. }
  have Hb0 : nth_error v (S y) = Some b0.
  { have : In (S y) (seq 0 (bound + 1)) by apply /in_seq; lia.
    move: IH' => /Forall_forall /[apply].
    move=> /type_assignmentE [>] /type_assignmentE [>] /type_assignmentE [>].
    rewrite Hx=> - [<- <-].
    move=> H'' /type_assignmentE [>].
    rewrite H2y /s_pos Nat.eqb_refl.
    have /Nat.eqb_neq -> : S y <> y by lia.
    move=> [<- <-]. case; last done. move=> ?. subst.
    move: H'' => /In_s_rule_spec [] //.
    move=> [] *. subst. apply: nth_error_nth'. lia. }
  move: Hr Ha0 Hb0 => /step_spec /[apply] /[apply] ?.
  apply: rt_trans. { apply: rt_step. eassumption. }
  apply: (IH N1).
  - move=> /=. lia.
  - move: H' H1N1 => /type_assignmentE [>] /In_Γ_allE /[apply].
    case=> // > [?????] _ _ => [| |_]; subst.
    all: move=> /nf_hf_atom; by apply.
  - by rewrite length_map length_seq.
  - apply /Forall_forall => i /[dup] /in_seq [_ ?].
    move: IH' => /Forall_forall /[apply].
    move=> /type_assignmentE [>] /type_assignmentE [>] /type_assignmentE [>].
    rewrite Hx=> - [<- <-].
    move=> H'x /type_assignmentE [>].
    rewrite H2y /s_pos.
    case E1iy: (Nat.eqb i y).
    { move=> [<- <-]. case; last done. move=> ? _. subst.
      move: H'x => /In_s_rule_spec [] //.
      move=> [? -> ??] + _. congr type_assignment. congr symbol.
      rewrite (map_nth' 0). { by rewrite length_seq Hv. }
      rewrite seq_nth /= ?E1iy; lia. }
    case E2iy: (Nat.eqb i (S y)).
    { move=> [<- <-]. case; last done. move=> ? _. subst.
      move: H'x => /In_s_rule_spec [] //.
      move=> [? -> ??] + _. congr type_assignment. congr symbol.
      rewrite (map_nth' 0). { by rewrite length_seq Hv. }
      rewrite seq_nth /= ?E1iy ?E2iy; lia. }
    move=> [<- <-]. case; last done. move=> ? _. subst.
    move: H'x => /In_s_rule_spec [] //.
    move=> e [? -> ??] ? + _. congr type_assignment. congr symbol.
    rewrite (map_nth' 0). { by rewrite length_seq Hv. }
    rewrite seq_nth /= ?E1iy ?E2iy; lia.
Qed.

(*if triangle is inhabited in (Γ_init ++ Γ_step rs), then 0..0 rewrites to 1..1*)
Theorem soundness N :
  normal_form N ->
  type_assignment (Γ_init ++ Γ_step) N triangle ->
  exists (m : nat), multi_step rs (repeat 0 (1+m)) (repeat 1 (1+m)).
Proof.
  move=> /nf_hf_atom + /[dup] => /[apply].
  move=> /soundness_init /[apply] - [N'] [] + [].
  move=> /(soundness_expand 0) /[apply] /[apply] => /(_ (Forall_nil _)).
  move=> [bound] [N''] [] /soundness_step H H'.
  exists bound. move: H'. have -> : 1 + bound = bound + 1 by lia.
  move=> H'. apply: H. { by rewrite repeat_length. }
  move: H' => /Forall_map. apply: Forall_impl => i.
  by rewrite nth_repeat.
Qed.

(* COMPLETENESS *)

(*hash, dollar is inhabited in Γ_all rs 0 [0, 1], then triangle is inhabited in (Γ_init ++ Γ_step rs)*)
Lemma completeness_init N :
  neutral normal_form N ->
  type_assignment (Γ_all 0 0) N hash ->
  type_assignment (Γ_all 0 1) N dollar ->
  exists N', normal_form N' /\ type_assignment (Γ_init ++ Γ_step) N' triangle.
Proof.
  move=> ???.
  exists (app (var 0) N). split. { do ? constructor. by apply: neutral_normal_form. }
  apply: type_assignment_app.
  - econstructor; [done|]. by left.
  - done.
  - by constructor.
Qed.

Lemma In_Γ_all_skip_lr bound n i : 
  nth_error (Γ_all bound i) (bound + n) = nth_error (Γ_init ++ Γ_step) n.
Proof.
  rewrite /Γ_all /Γ_lr [nth_error _ (bound + n)]nth_error_app2 length_map length_seq. { lia. }
  congr nth_error. lia.
Qed.

(*if stars, hash, dollar is inhabited in Γ_all rs bound [0..bound-1, bound, bound+1], then hash, dollar is inhabited in Γ_all rs 0 [0, 1]*)
Lemma completeness_expand bound N :
  neutral normal_form N ->
  Forall (fun (i : nat) => type_assignment (Γ_all bound i) N star) (seq 1 bound) ->
  type_assignment (Γ_all bound 0) N hash ->
  type_assignment (Γ_all bound (1 + bound)) N dollar ->
  exists N', 
    neutral normal_form N' /\
    type_assignment (Γ_all 0 0) N' hash /\ 
    type_assignment (Γ_all 0 1) N' dollar.
Proof.
  elim: bound N. { move=> *. eexists. by split; [eassumption|]. }
  move=> bound IH N HN H1N H2N H3N.
  apply: (IH (app (var (bound + 1)) (lam N))).
  - do ? constructor. by by apply: neutral_normal_form.
  - move: H1N => /= /Forall_cons_iff [_].
    rewrite -!seq_shift !map_map => /Forall_map H'N.
    apply /Forall_map. apply: Forall_impl H'N => ? H'N.
    apply: type_assignment_app.
    + econstructor; [by rewrite In_Γ_all_skip_lr|]. by left.
    + do ? constructor. move: H'N. by rewrite /Γ_all /= -seq_shift map_map.
    + done.
  - apply: type_assignment_app.
    + econstructor; [by rewrite In_Γ_all_skip_lr|]. right. by left.
    + do ? constructor. move: H1N => /Forall_cons_iff [+ _].
      by rewrite /Γ_all /= -seq_shift map_map.
    + done.
  - apply: type_assignment_app.
    + econstructor; [by rewrite In_Γ_all_skip_lr|]. right. right. by left.
    + do ? constructor. move: H2N. by rewrite /Γ_all /= -seq_shift map_map Γ_lr_bound_S.
    + do ? constructor. move: H3N. by rewrite /Γ_all /= -seq_shift map_map.
Qed.

Lemma completeness_0 bound N :
  neutral normal_form N ->
  Forall (fun (i : nat) => type_assignment (Γ_all bound i) N (symbol 0)) (seq 0 (S bound)) ->
  type_assignment (Γ_all bound (1 + bound)) N (symbol 1) ->
  exists N', 
    neutral normal_form N' /\
    Forall (fun (i : nat) => type_assignment (Γ_all bound i) N' star) (seq 1 bound) /\
    type_assignment (Γ_all bound 0) N' hash /\
    type_assignment (Γ_all bound (1 + bound)) N' dollar.
Proof.
  move=> ? /= /Forall_cons_iff [H1N H2N] H3N.
  exists (app (var (bound + 2)) N). do ? split.
  - do ? constructor. by apply: neutral_normal_form.
  - apply: Forall_impl H2N => ? ?. apply: type_assignment_app.
    + econstructor; [by rewrite In_Γ_all_skip_lr|]. by left.
    + done.
    + done.
  - apply: type_assignment_app.
    + econstructor; [by rewrite In_Γ_all_skip_lr|]. right. by left.
    + done.
    + done.
  - apply: type_assignment_app.
    + econstructor; [by rewrite In_Γ_all_skip_lr|]. right. right. by left.
    + done.
    + done.
Qed.

Lemma nth_Γ_lr i j bound : j < bound -> nth_error (Γ_all bound i) j = Some (s_pos i j).
Proof.
  move=> ?. rewrite /Γ_all /Γ_lr nth_error_app1. { by rewrite length_map length_seq. }
  by rewrite nth_error_map CD_facts.nth_error_seq.
Qed.

Lemma In_s_id_rulesI c a b a' b' :
  In c symbols -> In (arr' [bullet] (arr' [symbol c] (symbol c)))
    (arr' [isl] (arr' [symbol a'] (symbol a)) :: arr' [isr] (arr' [symbol b'] (symbol b)) :: s_id_rules).
Proof. move=> ?. do 2 right. apply /in_map_iff. by exists c. Qed.

Lemma completeness_step (bound : nat) (N : term) (v w : list nat) :
  step rs v w ->
  (forall i, In (nth i v 0) symbols) ->
  neutral normal_form N ->
  length v = bound + 1 ->
  type_assignment (Γ_all bound (1 + bound)) N (symbol 1) ->
  Forall (fun i => type_assignment (Γ_all bound i) N (symbol (nth i w 0))) (seq 0 (bound + 1)) ->
  exists N',
    neutral normal_form N' /\
    type_assignment (Γ_all bound (1 + bound)) N' (symbol 1) /\
    Forall (fun i => type_assignment (Γ_all bound i) N' (symbol (nth i v 0))) (seq 0 (bound + 1)).  
Proof.
  case=> u1 u2 a0 b0 a1 b1. rewrite !length_app /= => + ??? H1N H2N.
  move=> /(@In_split rule) [rs1] [rs2] Hrs.
  have ? : length u1 < bound by lia.
  pose x := bound + (length Γ_init + length rs1).
  have Hx : forall i, nth_error (Γ_all bound i) x = Some (s_rule ((a0, b0), (a1, b1))).
  { move=> i. rewrite /x /Γ_all /Γ_step Hrs map_app nth_error_app2 length_map length_seq. { lia. }
    have -> /= : forall n, bound + n - bound = n by lia.
    by rewrite nth_error_app2 length_map ?Nat.sub_diag. }
  exists (app (app (var x) (var (length u1))) N). do ? split.
  - do ? constructor. by apply: neutral_normal_form.
  - apply: type_assignment_app; [apply: type_assignment_app| |].
    + econstructor; [by rewrite Hx|]. apply: In_s_id_rulesI. apply /in_app_iff. do 2 right. by left.
    + econstructor; [rewrite nth_Γ_lr; [done|]|by left].
      rewrite /s_pos.
      have /Nat.eqb_neq -> : S bound <> 0 + length u1 by lia.
      by have /Nat.eqb_neq -> : S bound <> S (0 + length u1) by lia.
    + done.
    + done.
    + done.
  - apply /Forall_forall => i /[dup] /in_seq [_ ?].
    move: H2N => /Forall_forall /[apply].
    have [Hi|[Hi|Hi]] : (i < length u1 \/ i >= length u1 + 2) \/ i = length u1 \/ i = S (length u1) by lia.
    + move=> H'N. apply: type_assignment_app; [apply: type_assignment_app| |].
      * econstructor; [by rewrite Hx|]. by apply: In_s_id_rulesI.
      * econstructor; [rewrite nth_Γ_lr; [done|]| by left].
        rewrite /s_pos.
        have /Nat.eqb_neq -> : i <> length u1 by lia.
        by have /Nat.eqb_neq -> : i <> S (length u1) by lia.
      * done.
      * move: H'N. congr type_assignment. congr symbol.
        case: Hi => ?. { by do 2 (rewrite (@app_nth1 nat); first done). }
        do 2 (rewrite (@app_nth2 nat); first lia).
        by have ->: i - length u1 = S (S (i - length u1 - 2)) by lia.
      * done.
    + rewrite Hi (@app_nth2 nat). { done. }
      rewrite (@app_nth2 nat) ?Nat.sub_diag. { done. }
      move=> /= H'N. apply: type_assignment_app; [apply: type_assignment_app| |].
      * econstructor; [by rewrite Hx|]. by left.
      * econstructor; [rewrite nth_Γ_lr; [done|]| by left].
        by rewrite /s_pos Nat.eqb_refl.
      * done.
      * done.
      * done.
    + rewrite Hi (@app_nth2 nat). { lia. }
      rewrite (@app_nth2 nat). { lia. }
      have -> : S (length u1) - length u1 = 1 by lia.
      move=> /= H'N. apply: type_assignment_app; [apply: type_assignment_app| |].
      * econstructor; [by rewrite Hx|]. right. by left.
      * econstructor; [rewrite nth_Γ_lr; [done|]| by left].
        rewrite /s_pos Nat.eqb_refl.
        by have /Nat.eqb_neq -> : S (length u1) <> length u1 by lia.
      * done.
      * done.
      * done.
Qed.

Lemma step_symbols v w :
  step rs v w ->
  (forall i : nat, In (nth i v 0) symbols) ->
  (forall i : nat, In (nth i w 0) symbols).
Proof.
  case=> u1 u2 > Hr H i. move: (H i).
  have [Hi|[->|[->|Hi]]] : i < length u1 \/ i = length u1 \/ i = S (length u1) \/ i >= length u1 + 2 by lia.
  - by rewrite !(@app_nth1 nat).
  - move=> _. rewrite (@app_nth2 nat) ?Nat.sub_diag. { done. }
    apply /in_app_iff. left. apply /in_flat_map.
    eexists. split; [eassumption|].
    move=> /=. tauto.
  - move=> _. rewrite (@app_nth2 nat). { lia. }
    have -> : S (length u1) - length u1 = 1 by lia.
    apply /in_app_iff. left. apply /in_flat_map.
    eexists. split; [eassumption|].
    move=> /=. tauto.
  - rewrite (@app_nth2 nat). { lia. }
    rewrite (@app_nth2 nat). { lia. }
    by have -> : i - length u1 = S (S (i - length u1 - 2)) by lia.
Qed.

Lemma completeness_star (bound : nat) (N : term) (v : list nat) :
  multi_step rs v (repeat 1 (1+bound)) ->
  (forall i, In (nth i v 0) symbols) ->
  neutral normal_form N ->
  length v = bound + 1 ->
  type_assignment (Γ_all bound (1 + bound)) N (symbol 1) ->
  Forall (fun i => type_assignment (Γ_all bound i) N (symbol 1)) (seq 0 (bound + 1)) ->
  exists N',
    neutral normal_form N' /\
    type_assignment (Γ_all bound (1 + bound)) N' (symbol 1) /\
    Forall (fun i => type_assignment (Γ_all bound i) N' (symbol (nth i v 0))) (seq 0 (bound + 1)).  
Proof.
  move=> /clos_rt_rt1n_iff. move E: (repeat 1 (1+bound)) => w Hvw.
  elim: Hvw E N; clear v w.
  { move=> ? <- N ??? HN. exists N. split; [done|split;[done|]].
    apply: Forall_In_impl H => i /in_seq ?. congr type_assignment. congr symbol.
    rewrite (nth_indep _ 0 1). { rewrite repeat_length. lia. }
    by rewrite nth_repeat. }
  move=> v u w /[dup] /step_length_eq Hvu /[dup] /step_symbols H'vu.
  move=> /completeness_step H _ /[apply] + N /[dup] Hv /H'vu ++ /[dup] H'v.
  rewrite Hvu. do 5 move=> /[apply]. move=> [N'] [?] [? ?]. by apply: H; eassumption.
Qed.

Lemma completeness (m : nat) :
  multi_step rs (repeat 0 (1+m)) (repeat 1 (1+m)) ->
  exists N, normal_form N /\ type_assignment (Γ_init ++ Γ_step) N triangle.
Proof.
  have unnest : forall (A B C : Prop), A -> (B -> C) -> (A -> B) -> C by auto.
  move=> /completeness_star => /(_ (var (m + 3))).
  apply: (unnest). { move=> ?. rewrite nth_repeat. apply /in_app_iff. right. by left. }
  apply: (unnest). { by constructor. }
  apply: (unnest). { rewrite repeat_length. lia. }
  apply: (unnest). { by econstructor; [rewrite In_Γ_all_skip_lr|by left]. }
  apply: (unnest). { apply /Forall_forall => ??. by econstructor; [rewrite In_Γ_all_skip_lr|by left]. }
  move=> [N'] [+] [+] HN' => /completeness_0 /[apply].
  apply: (unnest). { move: HN'. have -> : m + 1 = S m by lia. apply: Forall_impl => ?. by rewrite nth_repeat. }
  move=> [N''] [+] [+] [+] => /completeness_expand /[apply] /[apply] /[apply].
  move=> [N'''] [?] [?] ?. by apply: completeness_init; eassumption.
Qed.

End Argument.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.IntersectionTypes.Util.CD_wn.

(* reduction from simple semi-Thue system 01 rewriting to intersection type inhabitation *)
Theorem reduction : SSTS01 ⪯ CD_INH.
Proof.
  exists (fun rs => (Γ_init ++ Γ_step rs, triangle)).
  intros rs. split.
  - intros [n Hn%completeness].
    destruct Hn as [N [? HN]].
    exists N. exact HN.
  - intros [N HN].
    destruct (weak_normalization HN) as [N' HN' H'N'].
    apply (soundness rs N').
    + exact H'N'.
    + exact (type_preservation HN' HN).
Qed.
