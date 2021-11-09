(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Constructions(s): 
    Halting Problem of One-Counter Machines (CM1_HALT) with denominators at most 4 encoded as 
    Uniform Boundedness of Deterministic, Flip-consistent, Length-preserving Stack Machines with Exchange
*)

Require Import Relation_Operators Operators_Properties Lia PeanoNat List.
Import ListNotations.

Require Undecidability.CounterMachines.CM1.
Module CM := CM1.
Require Undecidability.CounterMachines.Util.CM1_facts.
Module CM_facts := CM1_facts.

Require Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.SMX.
Require Import Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.SMX_facts.
Module SM := SMX.
From Undecidability.StackMachines.Util Require Import Facts Nat_facts List_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Local Arguments in_combine_l {A B l l' x y}.
Local Arguments in_combine_r {A B l l' x y}.

Inductive Prefix : Set := Try | Yes | No.

Inductive BasicState : Set :=
  (* is_bounded false ask boundedness, is_bounded true is positive answer *)
  | is_bounded : bool -> BasicState 
  (* #?i tries operation at index i; #+i performs operation at index i; #-i continues with next operation *)
  | index : Prefix -> CM.State -> BasicState
  (* $?i to increase counter for current operation index i;
    $+i has successfully increased counter for current operation index i;
    $-i failed to increase counter for current operation index i *)
  | increase : Prefix -> CM.State -> BasicState.

Inductive State : Set :=
  | basic_state : BasicState -> State
  (* goto n X Y travels in steps of size (n+1) over 0s
    if successful goes to X, on failure goes to Y *)
  | goto : nat -> BasicState -> BasicState -> State.

Inductive Symbol : Set := zero : Symbol | one : Symbol.

(* index action *)
Local Notation "'#? i" := (basic_state (index Try i)) (at level 50).
Local Notation "'#+ i" := (basic_state (index Yes i)) (at level 50).
Local Notation "'#- i" := (basic_state (index No i)) (at level 50).
Local Notation "#? i" := (index Try i) (at level 50).
Local Notation "#+ i" := (index Yes i) (at level 50).
Local Notation "#- i" := (index No i) (at level 50).

(* increase action *)
Local Notation "'$? i" := (basic_state (increase Try i)) (at level 50).
Local Notation "'$+ i" := (basic_state (increase Yes i)) (at level 50).
Local Notation "'$- i" := (basic_state (increase No i)) (at level 50).
Local Notation "$? i" := (increase Try i) (at level 50).
Local Notation "$+ i" := (increase Yes i) (at level 50).
Local Notation "$- i" := (increase No i) (at level 50).

(* bound action *)
Local Notation "'?|" := (basic_state (is_bounded false)).
Local Notation "'+|" := (basic_state (is_bounded true)).
Local Notation "?|" := (is_bounded false).
Local Notation "+|" := (is_bounded true).

(* tape symbols *)
Local Notation "§0" := (zero).
Local Notation "§1" := (one).

Local Notation "§0^ n" := (repeat §0 n) (at level 10, format "§0^ n").

Opaque Nat.add Nat.mul List.app List.repeat.

(* rewrite rules to simplify nat expressions *)
Definition nat_norm := (Nat.add_0_r, Nat.add_0_l, Nat.sub_0_r, Nat.sub_diag, Nat.mul_1_r, Nat.mul_1_l, Nat.mod_1_r).

(* rewrite rules to simplify list app expressions *)
Definition app_norm := 
  (app_nil_l, app_nil_r, @app_assoc', @repeat_appP, @repeat_app_appP, @repeat_singP _ §0, @cons_repeat_app _ §0).

Lemma list_symbol_shape (l: list Symbol) : (exists n, l = §0^n) \/ (exists n l', l = §0^n ++ [§1] ++ l').
Proof.
  elim: l; first by (left; exists 0).
  move=> [|] l +; last by (right; by exists 0, l).
  by move=> [[n ->] | [n] [l' ->]]; [left | right]; exists (1+n); [| exists l'].
Qed.

Section Reduction.
  Variable P : CM.Cm1.
  Variable capped_P : Forall (fun '(_, n) => n < 4) P.

  Definition iP : list (CM.State * (CM.State * nat)) := combine (seq 0 (length P)) P.

  Definition gotos : list (nat * BasicState * BasicState) :=
    (* goto n #+i #-i *)
    map (fun '(i, (j, n)) => (n, #+i, #-i)) iP ++
    (* goto #?(i+1)*)
    map (fun '(i, (j, n)) => (0, #?(1+(i:CM.State)), #?(1+(i:CM.State)))) iP ++
    (* goto $?i*)
    map (fun '(i, (j, n)) => (0, $?i, $?i)) iP ++
    (* goto $+i*)
    map (fun '(i, (j, n)) => (0, $+i, $+i)) iP ++
    (* goto $-i*)
    map (fun '(i, (j, n)) => (0, $-i, $-i)) iP ++
    (* goto +| *)
    [(0, +|, +|)].

  Definition igotos : list (nat * (CM.State * BasicState * BasicState)) :=
    combine (seq 0 (length gotos)) gotos.
    
  (* space required to remember a goto operation *)
  Definition G := length gotos + 4.

  Local Definition SMX := SM.SMX (State := State) (Symbol := Symbol).
  Local Definition Instruction := SM.Instruction (State := State) (Symbol := Symbol).
  Local Definition Config := SM.Config (State := State) (Symbol := Symbol).

  (* 1{?i}0 => 1{M n +i -i}0} : check divisibility by n+1*)
  Definition index_try_spec : nat * (CM.State * nat) -> Instruction :=
    (fun '(i, (j, n)) => (([§1], [§0], '#?i), ([§1], [§0], goto n (#+i) (#-i)), false)).
  
  (* {-i} -> {M 0 ?i+1 ?i+1} : next index on failure *)
  Definition index_no_spec : nat * (CM.State * nat) -> Instruction :=
    (fun '(i, (j, n)) => (([], [§0], '#-i), ([], [§0], goto 0 (#? (1+i)) (#? (1+i))), false)).
  
  (* r{+i}1l f-> l1{?j}r : next index on success *)
  Definition index_yes_spec_1 : nat * (CM.State * nat) -> Instruction :=
    (fun '(i, (j, n)) => (([], [§1], '#+i), ([], [§1], ('#? j)), true)).

  (* r{+i}0^(n+1)l f-> l1{M 0 ?Ii ?Ii}0^nr : step by n+1, increase by 1*)
  Definition index_yes_spec_n1 : nat * (CM.State * nat) -> Instruction :=
    (fun '(i, (j, n)) => (([], repeat §0 (1+n), '#+i), (repeat §0 n, [§1], goto 0 ($?i) ($?i)), true)).

  (* 01{?Ii} -> 1{M 0 +Ii +Ii}0 : increase success *)
  Definition increase_try_spec_0 : nat * (CM.State * nat) -> Instruction :=
    (fun '(i, (j, n)) => (([§1] ++ [§0], [], '$?i), ([§1], [§0], goto 0 ($+i) ($+i)), false)).
  
  (* 11{?Ii} -> 1{M 0 -Ii -Ii}0 : increase failure*)
  Definition increase_try_spec_1 : nat * (CM.State * nat) -> Instruction :=
    (fun '(i, (j, n)) => (([§1] ++ [§1], [], '$?i), ([§1], [§0], goto 0 ($-i) ($-i)), false)).

  (* l1{+Ii}r f-> r0{+i}l : report increase successful, continue *)
  Definition increase_yes_spec : nat * (CM.State * nat) -> Instruction :=
    (fun '(i, (j, n)) => (([§1], [], '$+i), ([], [§0], '#+i), true)).
  
  (* l1{-Ii}r f-> r0{M 0 +B +B}l : report increase failed, bound found *)
  Definition increase_no_spec : nat * (CM.State * nat) -> Instruction :=
    (fun '(i, (j, n)) => (([§1], [], '$-i), ([], [§0], goto 0 +| +|), true)).

  (* l{M n X Y}0^Gr -> l0^(G-2-i)10^i1{?B}r *)
  Definition goto_spec_G : _ -> Instruction := 
    (fun '(i, (n, X, Y)) => (([], §0^G, goto n X Y), ([§1] ++ §0^i ++ [§1] ++ §0^(G-2-i), [], '?|), true)).

  (* l{M n X Y}0^m 1r f-> r1{X/Y}0^ml *)
  Definition goto_spec_1 : nat -> (nat * (nat * BasicState * BasicState)) -> Instruction := 
    (fun m '(i, (n, X, Y)) => 
      (([], §0^m ++ [§1], goto n X Y), (§0^m, [§1], basic_state (if m mod (n+1) is 0 then X else Y)), true)).
  
  (* l0^(G-2-i)10^i1{+B}r -> 0^(n+1){M n X Y}0*)
  Definition bound_yes_spec : _ -> Instruction := 
    (fun '(i, (n, X, Y)) => (([§1] ++ §0^i ++ [§1] ++ §0^(G-2-i), [], '+|), (§0^(n+1), §0^(G-(n+1)), goto n X Y), false)).

  (* 1{?B}1 -> 1{+B}1 *)
  Definition bound_try_spec_1 : Instruction :=
    (([§1], [§1], '?|), ([§1], [§1], '+|), true).

  (* 1{?B}01 -> 1{+B}01 *)
  Definition bound_try_spec_01 : Instruction :=
    (([§0] ++ [§1], [§1], '?|), ([§0] ++ [§1], [§1], '+|), true).

  (* 1{?B}00 -> 1{?0}01 *)
  Definition bound_try_spec_00 : Instruction :=
    (([§0] ++ [§0], [§1], '?|), ([§0] ++ [§1], [§1], '#?0), true).

  Definition bound_try_spec : list Instruction :=
    [bound_try_spec_1] ++ [bound_try_spec_01] ++ [bound_try_spec_00].

  Definition index_ops : list Instruction :=
    map index_try_spec iP ++ map index_no_spec iP ++ map index_yes_spec_1 iP ++ map index_yes_spec_n1 iP.
  
  Definition increase_ops : list Instruction :=
    map increase_try_spec_0 iP ++ map increase_try_spec_1 iP ++ map increase_yes_spec iP ++ map increase_no_spec iP.

  Definition goto_ops : list Instruction :=
    map goto_spec_G igotos ++ flat_map (fun m => map (goto_spec_1 m) igotos) (seq 0 G).

  Definition bound_ops : list Instruction :=
    map bound_yes_spec igotos ++ bound_try_spec.

  (* stack machine instuctions *)
  Definition M : SMX :=
    locked index_ops ++ locked increase_ops ++ locked goto_ops ++ locked bound_ops.

  (* infrastructure hints *)
  Lemma in_index_try_spec_M {i j n} : In (i, (j, n)) iP -> In (index_try_spec (i, (j, n))) M.
  Proof. move=> ?. rewrite /M -[locked index_ops]lock. apply /in_app_l /in_app_l /in_map_iff. by eexists. Qed.
  
  Lemma in_index_no_spec_M {i j n} : In (i, (j, n)) iP -> In (index_no_spec (i, (j, n))) M.
  Proof. move=> ?. rewrite /M -[locked index_ops]lock. apply /in_app_l /in_app_r /in_app_l /in_map_iff. by eexists. Qed.
  
  Lemma in_index_yes_spec_1_M {i j n} : In (i, (j, n)) iP -> In (index_yes_spec_1 (i, (j, n))) M.
  Proof. move=> ?. rewrite /M -[locked index_ops]lock. apply /in_app_l /in_app_r /in_app_r /in_app_l /in_map_iff. by eexists. Qed.
  
  Lemma in_index_yes_spec_n1_M {i j n} : In (i, (j, n)) iP -> In (index_yes_spec_n1 (i, (j, n))) M.
  Proof. move=> ?. rewrite /M -[locked index_ops]lock. apply /in_app_l /in_app_r /in_app_r /in_app_r /in_map_iff. by eexists. Qed.

  Lemma in_bound_try_spec_1_M : In bound_try_spec_1 M.
  Proof. rewrite /M -[locked bound_ops]lock. do 4 (apply /in_app_r). apply /in_app_l. by left. Qed.

  Lemma in_bound_try_spec_01_M : In bound_try_spec_01 M.
  Proof. rewrite /M -[locked bound_ops]lock. do 5 (apply /in_app_r). apply /in_app_l. by left. Qed.

  Lemma in_bound_try_spec_00_M : In bound_try_spec_00 M.
  Proof. rewrite /M -[locked bound_ops]lock. do 6 (apply /in_app_r). by left. Qed.

  Lemma in_bound_yes_spec_M {i n X Y} : In (i, (n, X, Y)) igotos -> In (bound_yes_spec (i, (n, X, Y))) M.
  Proof. move=> ?. rewrite /M -[locked bound_ops]lock. do 3 (apply /in_app_r). apply /in_app_l /in_map_iff. by eexists. Qed.
    
  Lemma in_increase_try_spec_0_M {i j n} : In (i, (j, n)) iP -> In (increase_try_spec_0 (i, (j, n))) M.
  Proof. move=> ?. rewrite /M -[locked increase_ops]lock. apply /in_app_r /in_app_l /in_app_l /in_map_iff. by eexists. Qed.

  Lemma in_increase_try_spec_1_M {i j n} : In (i, (j, n)) iP -> In (increase_try_spec_1 (i, (j, n))) M.
  Proof. move=> ?. rewrite /M -[locked increase_ops]lock. apply /in_app_r /in_app_l /in_app_r /in_app_l /in_map_iff. by eexists. Qed.

  Lemma in_increase_yes_spec_M {i j n} : In (i, (j, n)) iP -> In (increase_yes_spec (i, (j, n))) M.
  Proof. move=> ?. rewrite /M -[locked increase_ops]lock. apply /in_app_r /in_app_l /in_app_r /in_app_r /in_app_l /in_map_iff. by eexists. Qed.
  
  Lemma in_increase_no_spec_M {i j n} : In (i, (j, n)) iP -> In (increase_no_spec (i, (j, n))) M.
  Proof. move=> ?. rewrite /M -[locked increase_ops]lock. apply /in_app_r /in_app_l /in_app_r /in_app_r /in_app_r /in_map_iff. by eexists. Qed.

  Lemma in_goto_spec_1_M {m i n X Y} : m < G -> In (i, (n, X, Y)) igotos -> In (goto_spec_1 m (i, (n, X, Y))) M.
  Proof.
    move=> ? ?. apply /in_app_r /in_app_r /in_app_l. rewrite -lock. 
    apply /in_app_r /in_flat_map. exists m. constructor; [by apply /in_seq; lia | by apply /in_map]. 
  Qed.

  Lemma in_goto_spec_G_M {i n X Y} : In (i, (n, X, Y)) igotos -> In (goto_spec_G (i, (n, X, Y))) M.
  Proof. move=> ?. rewrite /M -[locked goto_ops]lock. do 2 (apply /in_app_r). apply /in_app_l /in_app_l /in_map_iff. by eexists. Qed.

  Lemma in_scan_gotos {i j n} : In (i, (j, n)) iP -> In (n, #+i, #-i) gotos.
  Proof. move=> ?. apply /in_app_l /in_map_iff. eexists. by constructor; last by eassumption. Qed.
  
  Lemma in_next_gotos {i j n} : In (i, (j, n)) iP -> In (0, #?(1+i), #?(1+i)) gotos.
  Proof. move=> ?. do 1 (apply /in_app_r). apply /in_app_l /in_map_iff. eexists. by constructor; last by eassumption. Qed.

  Lemma in_try_gotos {i j n} : In (i, (j, n)) iP -> In (0, $?i, $?i) gotos.
  Proof. move=> ?. do 2 (apply /in_app_r). apply /in_app_l /in_map_iff. eexists. by constructor; last by eassumption. Qed.

  Lemma in_yes_gotos {i j n} : In (i, (j, n)) iP -> In (0, $+i, $+i) gotos.
  Proof. move=> ?. do 3 (apply /in_app_r). apply /in_app_l /in_map_iff. eexists. by constructor; last by eassumption. Qed.

  Lemma in_no_gotos {i j n} : In (i, (j, n)) iP -> In (0, $-i, $-i) gotos.
  Proof. move=> ?. do 4 (apply /in_app_r). apply /in_app_l /in_map_iff. eexists. by constructor; last by eassumption. Qed.

  Lemma in_bound_gotos : In (0, +|, +|) gotos.
  Proof. do 5 (apply /in_app_r). by left. Qed.

  Local Hint Immediate 
    in_goto_spec_1_M in_goto_spec_G_M
    in_index_try_spec_M in_index_no_spec_M in_index_yes_spec_1_M in_index_yes_spec_n1_M
    in_increase_try_spec_0_M in_increase_try_spec_1_M in_increase_yes_spec_M in_increase_no_spec_M
    in_bound_try_spec_1_M in_bound_try_spec_01_M in_bound_try_spec_00_M in_bound_yes_spec_M
    in_scan_gotos in_next_gotos in_try_gotos in_yes_gotos in_no_gotos in_bound_gotos
      : M.

  Inductive step_spec (X Y: Config) : Prop :=
  | index_try_step_spec v w i j n : 
    X = ([§1] ++ v, [§0] ++ w, '#?i) -> Y = ([§1] ++ v, [§0] ++ w, goto n (#+i) (#-i)) -> 
    In (i, (j, n)) iP -> step_spec X Y
  | index_no_step_spec v w i j n : 
    X = (v, [§0] ++ w, '#-i) -> Y = (v, [§0] ++ w, goto 0 (#? (1+i)) (#? (1+i))) -> 
    In (i, (j, n)) iP -> step_spec X Y
  | index_yes_step_spec_1 v w i j n : 
    X = (v, [§1] ++ w, '#+i) -> Y = ([§1] ++ w, v, '#?j) -> 
    In (i, (j, n)) iP -> step_spec X Y
  | index_yes_step_spec_n1 v w i j n : 
    X = (v, repeat §0 (1+n) ++ w, '#+i) -> Y = ([§1] ++ w, repeat §0 n ++ v, goto 0 ($?i) ($?i)) -> 
    In (i, (j, n)) iP -> step_spec X Y
  | increase_try_step_spec_0 v w i j n : 
    X = ([§1] ++ [§0] ++ v, w, '$?i) -> Y = ([§1] ++ v, [§0] ++ w, goto 0 ($+i) ($+i)) -> 
    In (i, (j, n)) iP -> step_spec X Y
  | increase_try_step_spec_1 v w i j n : 
    X = ([§1] ++ [§1] ++ v, w, '$?i) -> Y = ([§1] ++ v, [§0] ++ w, goto 0 ($-i) ($-i)) -> 
    In (i, (j, n)) iP -> step_spec X Y
  | increase_yes_step_spec v w i j n : 
    X = ([§1] ++ v, w, '$+i) -> Y = ([§0] ++ w, v, '#+i) -> 
    In (i, (j, n)) iP -> step_spec X Y
  | increase_no_step_spec v w i j n : 
    X = ([§1] ++ v, w, '$-i) -> Y = ([§0] ++ w, v, goto 0 +| +|) -> 
    In (i, (j, n)) iP -> step_spec X Y
  | goto_step_spec_G v w i n' X' Y' : 
    X = (v, §0^G ++ w, goto n' X' Y') -> Y = (w, [§1] ++ §0^i ++ [§1] ++ §0^(G-2-i) ++ v, '?|) -> 
    In (i, (n', X', Y')) igotos -> step_spec X Y
  | goto_step_spec_1 v w m i n' X' Y' : 
    X = (v, §0^m ++ [§1] ++ w, goto n' X' Y') -> Y = ([§1] ++ w, §0^m ++ v, basic_state (if m mod (n'+1) is 0 then X' else Y')) -> 
    In (i, (n', X', Y')) igotos -> m < G -> step_spec X Y
  | bound_yes_step_spec v w i n' X' Y' : 
    X = ([§1] ++ §0^i ++ [§1] ++ §0^(G-2-i) ++ v, w, '+|) -> Y = (§0^(n'+1) ++ v, §0^(G-(n'+1)) ++ w, goto n' X' Y') -> 
    In (i, (n', X', Y')) igotos -> step_spec X Y
  | bound_try_step_spec_1 v w : 
    X = ([§1] ++ v, [§1] ++ w, '?|) -> Y = ([§1] ++ w, [§1] ++ v, '+|) -> step_spec X Y
  | bound_try_step_spec_01 v w : 
    X = ([§0] ++ [§1] ++ v, [§1] ++ w, '?|) -> Y = ([§1] ++ w, [§0] ++ [§1] ++ v, '+|) -> step_spec X Y
  | bound_try_step_spec_00 v w : 
    X = ([§0] ++ [§0] ++ v, [§1] ++ w, '?|) -> Y = ([§1] ++ w, [§0] ++ [§1] ++ v, '#?0) -> step_spec X Y.

  Lemma stepE X Y : SM.step M X Y -> step_spec X Y.
  Proof.
    case=> >. rewrite /M ?in_app_iff -?lock. move=> [|[|[|]]].
    - rewrite /index_ops ?in_app_iff ?in_map_iff. 
      move=> [|[|[|]]] [[? [? ?]]] [[]] *; subst; by eauto using step_spec.
    - rewrite /increase_ops ?in_app_iff ?in_map_iff. 
      move=> [|[|[|]]] [[? [? ?]]] [[]] *; subst; rewrite ?app_norm; by eauto using step_spec.
    - rewrite /goto_ops ?in_app_iff in_flat_map ?in_map_iff. move=> [|].
      + move=> [[? [[? ?] ?]]] [[]] *. subst. rewrite ?app_norm. by eauto using step_spec.
      + move=> [?]. rewrite in_seq in_map_iff. move=> [[? ?]] [[? [[? ?] ?]]] [[]] *. subst.
        rewrite ?app_norm. by eauto using step_spec.
    - rewrite /bound_ops ?in_app_iff in_map_iff. move=> [|].
      + move=> [[? [[? ?] ?]]] [[]] *. subst. rewrite ?app_norm. by eauto using step_spec.
      + move=> [|[|]]; (case; last done); move=> [] *; subst; rewrite -?app_assoc; by eauto using step_spec.
  Qed.

  Local Definition reachable_n := reachable_n M.

  Lemma iP_capped {i j n}: In (i, (j, n)) iP -> n < 4.
  Proof using capped_P. move /in_combine_r. have /Forall_forall := capped_P. by move=> H /H. Qed.

  Lemma gotos_igotos {n X Y} : In (n, X, Y) gotos -> exists i, In (i, (n, X, Y)) igotos.
  Proof. move /(In_nth_error gotos) => [i /nth_error_Some_In_combineP ?]. by exists i. Qed.

  Lemma igotos_capped {i n X Y} : In (i, (n, X, Y)) igotos -> n < 4.
  Proof using capped_P.
    move /in_combine_r. rewrite /gotos ?in_app_iff ?in_map_iff.
    case; first by (move=> [[? [? ?]]] [[]] *; subst; apply: iP_capped; eassumption).
    do 4 (case; first by (move=> [[? [? ?]]] [[]] *; subst; lia)).
    case; last done. case=> *. by lia.
  Qed.

  Lemma nth_error_Some_In_iP {i j n} : nth_error P i = Some (j, n) <-> In (i, (j, n)) iP.
  Proof. by apply: nth_error_Some_In_combineP. Qed.

  Lemma in_iPI {i} : i < length P -> exists j n, In (i, (j, n)) iP.
  Proof.
    move H: (nth_error P i) => x ?. case: x H; last by (move /nth_error_None; lia).
    move=> [j n] /nth_error_Some_In_iP ?. by exists j, n.
  Qed.

  Lemma not_in_iPI {i x} : length P <= i -> not (In (i, x) iP).
  Proof. move=> ? /in_combine_l /in_seq. by lia. Qed.

  Lemma in_iP_unique {i j n j' n'} : 
    In (i, (j, n)) iP -> In (i, (j', n')) iP -> j = j' /\ n = n'.
  Proof. move=> /nth_error_Some_In_iP + /nth_error_Some_In_iP => -> [-> ->]. by constructor. Qed.

  Lemma in_igotos_unique {i n X Y n' X' Y'} : 
    In (i, (n, X, Y)) igotos -> In (i, (n', X', Y')) igotos -> n = n' /\ X = X' /\ Y = Y'.
  Proof. move=> /nth_error_Some_In_combineP + /nth_error_Some_In_combineP => -> [] *. by subst. Qed.

  Lemma length_iP : length iP = length P.
  Proof. by rewrite /iP combine_length seq_length Nat.min_id. Qed.

  Definition gotos_index (X Y: BasicState ) : nat :=
    match X, Y with
    | #+ i, #- j => i
    | #? i, #? j => length P + (i-1)
    | $? i, $? j => length P * 2 + i
    | $+ i, $+ j => length P * 3 + i
    | $- i, $- j => length P * 4 + i
    | _, _ => length P * 5
    end.

  Lemma nth_error_iP_Some {i} : i < length iP -> exists j n, nth_error iP i = Some (i, (j, n)).
  Proof. rewrite length_iP. move /in_iPI => [j [n /nth_error_Some_In_combineP /nth_error_combine_SomeP ?]]. by exists j, n. Qed.

  Lemma gotos_indexP {i n X Y} : nth_error gotos i = Some (n, X, Y) -> i = gotos_index X Y.
  Proof.
    have ? := length_iP. case /nth_error_appP.
    { rewrite map_length nth_error_map. by move=> [/nth_error_iP_Some [? [? ->]]] [] _ <- <-. }
    do 4 (rewrite map_length => [[?]]; case /nth_error_appP; 
      first by rewrite map_length nth_error_map; move=> [/nth_error_iP_Some [? [? ->]]] [] _ <- <- /=; lia).
    rewrite map_length. move Hi': (i' in nth_error _ i') => i'. move: i' Hi' => [|i'] /=; last by (case: i' => > ? [? ?]).
    move=> ? [?] [] _ <- <- /=. by lia.
  Qed.

  Lemma in_igotos_unique_index {i i' n X Y} : 
    In (i, (n, X, Y)) igotos -> In (i', (n, X, Y)) igotos -> i = i'.
  Proof. by move=> /nth_error_Some_In_combineP /gotos_indexP + /nth_error_Some_In_combineP /gotos_indexP => <-. Qed.

  Lemma state_flip {s t X c b} : In ((s, t, X), c, b) M ->
    match X with
    | ('#? _) | ('#- _) | ('$? _) | ('+|) => b = false
    | _ => b = true
    end.
  Proof.
    rewrite /M ?in_app_iff -?lock. move=> [|[|[|]]].
    - rewrite /index_ops ?in_app_iff ?in_map_iff.
      by move=> [|[|[|]]] [[? [? ?]]] [[]] *; subst.
    - rewrite /increase_ops ?in_app_iff ?in_map_iff.
      by move=> [|[|[|]]] [[? [? ?]]] [[]] *; subst.
    - rewrite /goto_ops ?in_app_iff in_flat_map. 
      move=> [| [?] [_]]; rewrite in_map_iff; move=> [[? [[? ?] ?]]] [[]] *; by subst.
    - case /in_app_iff.
      + move=> /in_map_iff [[? [[? ?] ?]]] [[]] *. by subst.
      + case; [| case; [| case; [|done]]]; move=> [] *; by subst.
  Qed.

  Lemma in_igotos_lt {i x} : In (i, x) igotos -> i < length gotos.
  Proof. move /in_combine_l /in_seq. by lia. Qed.

  Lemma zero_prefix_lt {n m v w} : §0^n ++ [§1] ++ v = §0^m ++ w -> m <= n.
  Proof.
    elim: m n; first by lia.
    move=> m IH [|n]; first done.
    have H : forall k, §0^(S k) = [§0] ++ §0^k by (move=> ?; rewrite ?app_norm).
    rewrite ?H -?app_assoc. move /app_inv_head /IH. by lia.
  Qed.

  Lemma zero_prefix_eq {n m v1 v2} : §0^n ++ [§1] ++ v1 = §0^m ++ [§1] ++ v2 -> n = m.
  Proof. move /copy => [/zero_prefix_lt + /esym /zero_prefix_lt]. by lia. Qed.

  Lemma contradict_G_prefix {v1 v2 n} : §0^G ++ v1 = §0^n ++ [§1] ++ v2 -> n < G -> False.
  Proof. move=> /esym /zero_prefix_lt. by lia. Qed.

  (* end of infrastructure code *)

  Local Definition transition := SM.transition (State := State) (Symbol := Symbol).

  Theorem flip_consistent_M {s1 t1 X c b1 s2 t2 c2 b2} : 
    In ((s1, t1, X), c, b1) M -> In ((s2, t2, X), c2, b2) M -> b1 = b2.
  Proof.
    move=> /state_flip + /state_flip. case: X; last by congruence.
    case; (case; by congruence).
  Qed.

  (* identifies matching iP instructions *)
  Ltac unify_iP :=
    match goal with H1 : In (?i, (?j1, ?n1)) iP, H2 : In (?i, (?j2, ?n2)) iP |- _ => 
      have [? ?]:= in_iP_unique H1 H2; subst; clear H1 H2
    end.

  (* identifies matching igotos instructions *) 
  Ltac unify_igotos :=
    match goal with 
    | H1 : In (?i, (?n1, ?X1, ?Y1)) igotos, H2 : In (?i, (?n2, ?X2, ?Y2)) igotos |- _ => 
        have [? [? ?]] := in_igotos_unique H1 H2; subst; clear H1 H2
    | H1 : In (?i1, (?n, ?X, ?Y)) igotos, H2 : In (?i2, (?n, ?X, ?Y)) igotos |- _ => 
      have ? := in_igotos_unique_index H1 H2; subst; clear H1 H2
    end.

  (* simplifies app equalities *)
  Ltac unify_app :=
  match goal with
  | H : ?l ++ ?l1 = ?l ++ ?l2 |- _ => 
    move /app_inv_head in H; subst
  | H : ?a :: ?l1 = ?a :: ?l2 |- _ => 
    (have ? : l1 = l2 by congruence); subst; clear H
  | H : §0^?n ++ (§1 :: ?v1) = §0^?m ++ (§1 :: ?v2) |- _ =>
    have ? := zero_prefix_eq H; subst
  | H1 : §0^G ++ ?v1 = §0^?n ++ (§1 :: ?v2), H2 : ?n < G |- _ =>
    have ? := contradict_G_prefix H1 H2; clear H1 H2
  | H1 : §0^?n ++ (§1 :: ?v2) = §0^G ++ ?v1, H2 : ?n < G |- _ =>
    have ? := contradict_G_prefix (esym H1) H2; clear H1 H2
  end.

  Theorem deterministic_M : SM.deterministic M. 
  Proof.
    move=> X Y Z + /stepE [] > H2X -> * => /stepE [] > H1X -> *; 
      move: H2X H1X => -> []; rewrite ?app_singP ?app_repeat_cons /=; try congruence; move=> *; subst.
    all: (do ? unify_iP); (do ? unify_app); (do ? unify_igotos); try by [| congruence].
  Qed.

  Theorem length_preserving_M {s t X s' t' Y b} :
    In ((s, t, X), (s', t', Y), b) M -> length (s ++ t) = length (s' ++ t') /\ 1 <= length (s ++ t).
  Proof using capped_P.
    move /(transition _ [] []). rewrite ?app_norm.
    move: b => [|] /stepE [] > + [] *; move=> [] *; subst; rewrite ?app_length ?repeat_length ?/G /=.
    all: try by lia.
    all: have := in_igotos_lt ltac:(eassumption); have ? := igotos_capped ltac:(eassumption); by lia.
  Qed.

  (* starting CM1 configuration *)
  Definition cm_start : CM.Config := {| CM.state := 0; CM.value := 1 |}.

  (* successful bound search up to space C *)
  Definition bound_reachable_n (C N: nat) : Prop :=
    forall m l r, m <= C ->
      reachable_n N (repeat §0 m ++ [§1] ++ r, [§1] ++ l, '?|) ([§1] ++ l, repeat §0 m ++ [§1] ++ r, '+|).

  Definition goto_time (C N: nat) := (C+1)*(N+3).
  (* goto 1 and switch to X/Y depending on c mod (n+1) *)
  (* C is inductive argument for external bound lemma *)
  Lemma goto_1 {C N: nat} : bound_reachable_n C N ->
    forall l r i n X Y c, In (i, (n, X, Y)) igotos -> (c - G) <= C ->
    reachable_n (goto_time C N)
      (l, §0^c ++ [§1] ++ r, goto n X Y) 
      ([§1] ++ r, §0^c ++ l, basic_state (if c mod (n+1) is 0 then X else Y)).
  Proof using capped_P.
    move=> HN l r i n X Y c Hi HC. 
    suff: reachable_n ((c+1-G)*(N+2)+1) (* actual inductive lemma *)
      (l, §0^c ++ [§1] ++ r, goto n X Y) 
      ([§1] ++ r, §0^c ++ l, basic_state (if c mod (n+1) is 0 then X else Y)).
    { apply: reachable_n_mon'; [ by (rewrite /goto_time; nia) | done ]. }
    
    elim /(measure_ind id): c l r HC => c IH l r HcC.
    have [HcG | HcG]: c < G \/ c >= G by lia.
      (* case c < G *)
    { apply: (first_step (goto_spec_1 c (i, (n, X, Y))) l r);
        [by lia | by auto with M | by rewrite ?app_norm | by apply: reach_refl ]. }
    (* case c >= G *)
    apply: (first_step (goto_spec_G (i, (n, X, Y))) l (§0^(c-G) ++ [§1] ++ r));
      [ by nia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia | ].

    have := HN (c - G) (§0^i ++ [§1] ++ §0^(G - 2 - i) ++ l) r ltac:(lia).
    apply: (reachable_n_trans' ((c-G)*(N+2)+2)); [ by nia | by rewrite ?app_norm | ].

    apply: (first_step (bound_yes_spec (i, (n, X, Y))) l (§0^(c - G) ++ [§1] ++ r));
      [ by nia | by auto with M | by rewrite ?app_norm | ].

    have ? : G >= 4 by rewrite /G; lia.
    have := IH (c - (n+1)) ltac:(lia) (§0^(n+1) ++ l) r ltac:(lia).
    apply: reachable_n_mon'; first by lia.
    
    rewrite ?app_norm. have ? := igotos_capped Hi.
    have Hcn : c - (n + 1) + (n + 1) = c by lia.
    have -> : (c - (n + 1)) mod (n + 1) = c mod (n + 1).
    {
      rewrite -[in RHS]Hcn Nat.add_mod; first by lia.
      rewrite Nat.mod_same; first by lia. by rewrite ?nat_norm Nat.mod_mod; first by lia.
    }
    by do 5 f_equal; lia.
  Qed.

  (* goto 1 and switch to X/Y depending on c mod (n+1) *)
  (* C is inductive argument for external bound lemma *)
  Lemma first_goto_1 {C N: nat} : bound_reachable_n C N ->
    forall (T: nat) (l r: list Symbol) T' n X Y c Z, In (n, X, Y) gotos -> (c - G) <= C -> T + goto_time C N <= T' ->
    reachable_n T ([§1] ++ r, §0^c ++ l, basic_state (if c mod (n+1) is 0 then X else Y)) Z ->
    reachable_n T' (l, §0^c ++ [§1] ++ r, goto n X Y) Z.
  Proof using capped_P.
    move=> HN T l r T' > /gotos_igotos [?] /(goto_1 HN l r) H => /H => + ? ?.
    by apply: (reachable_n_trans' T); first by lia.
  Qed.

  Arguments first_goto_1 {C N} _ T {l r T' n X Y c Z}. 

  Definition increase_time (C N: nat) := (C+G+2)*(2*(goto_time C N)+3).

  (* for each §0^(n+1) on the right shift §1 on the left *)
  Lemma do_increase {C N: nat} : bound_reachable_n C N ->
    forall l r i j n k m, In (i, (j, n)) iP -> m + k * (2+n) - (G + 1) <= C ->
    reachable_n ((k+1)*(2*(goto_time C N)+3))
      (§0^m ++ [§1] ++ §0^k ++ l, §0^(k * (1+n)) ++ r, '#+i) 
      (§0^(m + k * (2+n)) ++ [§1] ++ l, r, '#+i).
  Proof using capped_P.
    move=> HN l r i j n k m Hijn. elim: k m l r.
      (* case k = 0 *)
    { move=> m l r _. rewrite ?app_norm ?nat_norm. by apply: reach_refl. }
    (* case k > 0 *)
    move=> k IH m l r HmkC. have ? := iP_capped Hijn.
    pose N' := (k+1)*(2 * goto_time C N + 3).
    apply: (first_step (index_yes_spec_n1 (i, (j, n))) (§0^m ++ [§1] ++ §0^(1+k) ++ l) (§0^(k * (1 + n)) ++ r));
      [by lia | by auto with M | by rewrite ?app_norm |].

    rewrite ?app_norm. apply: (first_goto_1 HN (N' + goto_time C N + 2)); 
      [ by eauto with M | by lia | by lia |].

    apply: (first_step (increase_try_spec_0 (i, (j, n))) (§0^k ++ l) (§0^(n + m) ++ [§1] ++ §0^(k * (1 + n)) ++ r));
      [by lia | by auto with M | by rewrite ?app_norm |].

    rewrite ?app_norm. apply: (first_goto_1 HN (N' + 1));
      [ by eauto with M | by lia | by lia |].

    apply: (first_step (increase_yes_spec (i, (j, n))) (§0^(k * (1 + n)) ++ r) (§0^(1 + (n + m)) ++ [§1] ++ §0^k ++ l));
      [by lia | by auto with M | by rewrite ?app_norm |].

    have := IH (m + n + 2) l r ltac:(lia). apply: reachable_n_mon'; 
      [by lia | by rewrite ?app_norm; do 5 f_equal; lia].
  Qed.

  Arguments do_increase {C N} _ l r {i j n} k m.

  (* not enough space to set counter value to c / (n+1) * (n+2) *)
  Lemma fail_increase {C N: nat} : bound_reachable_n C N ->
    forall l r i j n k, In (i, (j, n)) iP -> (k+1) * (2+n) - (G + 1) <= C ->
    reachable_n (increase_time C N) 
      ([§1] ++ §0^k ++ [§1] ++ l, §0^((k+1)*(1+n)) ++ r, '#+i) 
      ([§1] ++ l, §0^((k+1)*(1+n) + k) ++ [§1] ++ r, goto 0 ($-i) ($-i)).
  Proof using capped_P.
    move=> HN l r i j n k Hijn HC. rewrite /increase_time.
    have := do_increase HN ([§1] ++ l) (§0^(1 + n) ++ r) k 0 Hijn ltac:(lia).
    apply: (reachable_n_trans' (2 * goto_time C N + 3)); first by ((suff: k+1 <= C + G + 1 by nia); lia).
    { rewrite ?app_norm ?nat_norm. do 4 f_equal. by lia. }

    apply: (first_step (index_yes_spec_n1 (i, (j, n))) (§0^(k * (2 + n)) ++ [§1] ++ [§1] ++ l) r);
      [by lia | by auto with M | by rewrite ?app_norm |].

    rewrite ?app_norm. apply: (first_goto_1 HN (goto_time C N + 2));
      [ by eauto with M | by lia | by lia | ].

    apply: (first_step (increase_try_spec_1 (i, (j, n))) l (§0^(n + k * (2 + n)) ++ [§1] ++ r));
      [by lia | by auto with M | by rewrite ?app_norm | ].
    apply: reachable_n_refl'. rewrite ?app_norm. do 4 f_equal. by lia.
  Qed.

  Definition step_time (C N: nat) := goto_time C N + increase_time C N + 1.

  Lemma do_cm_step {C N: nat} : bound_reachable_n C N -> forall l r p, CM.value (CM1.step P p) <= G + C ->
    reachable_n (step_time C N) 
      ([§1] ++ l, §0^(CM.value p) ++ [§1] ++ (§0^(CM.value (CM1.step P p) - CM.value p)) ++ r, '#?(CM.state p))
      ([§1] ++ l, §0^(CM.value (CM1.step P p)) ++ [§1] ++ r, '#?(CM.state (CM1.step P p))).
  Proof using capped_P.
    move=> HN l r [i [|c]] /= HpC; first by apply: reach_refl.
    (* case c > 0 *)
    move H: (nth_error P i) HpC => oi. case: oi H; first last.
    { move=> _ _ /=. rewrite ?nat_norm ?app_norm. by apply: reach_refl. }
    move=> [j n] /nth_error_Some_In_iP. rewrite /step_time.
    move Hm: (S c mod (n + 1)) => m. move: m Hm => [|m] Hcn /= Hijn.
    (* case n+1 divides c *)
    - have := mod_frac_lt Hcn. move Hd: (S c * (n + 2) / (n + 1)) => d Hcd HC.

      apply: (first_step (index_try_spec (i, (j, n))) l (§0^c ++ [§1] ++ §0^(d - S c) ++ r)); 
        [ by lia | by auto with M | by rewrite ?app_norm | ].

      rewrite ?app_norm. apply: (first_goto_1 HN (increase_time C N)); 
        [ by eauto with M | by lia | by lia |].
      rewrite Hcn. have ? := divides_frac_diff Hcn.
      
      have := do_increase HN r ([§1] ++ l) (d - S c) 0 Hijn ltac:(lia).
      apply: (reachable_n_trans' 1); 
        [ by rewrite /increase_time; nia | by rewrite ?app_norm; do 4 f_equal; lia |].
      
      apply: (first_step (index_yes_spec_1 (i, (j, n))) (§0^((d - S c) * (2 + n)) ++ [§1] ++ r) l);
        [ by lia | by auto with M | by rewrite ?app_norm | ].
        
      apply: reachable_n_refl'. rewrite ?app_norm. by do 4 f_equal; lia.
    (* case n+1 does not divide c *)
    - move=> ?.
      apply: (first_step (index_try_spec (i, (j, n))) l (§0^c ++ [§1] ++ r));
        [by lia | by auto with M | by rewrite ?app_norm ?nat_norm | ].

      rewrite ?app_norm. apply: (first_goto_1 HN (increase_time C N)); 
        [ by eauto with M | by lia | by lia | rewrite Hcn /increase_time ].
      
      apply: (first_step (index_no_spec (i, (j, n))) ([§1] ++ r) (§0^c ++ [§1] ++ l));
        [ by lia | by auto with M | done |].

      rewrite ?app_norm. apply: (first_goto_1 HN 0); 
        [ by eauto with M | by lia | by lia | by apply: reach_refl].
  Qed.
    
  Lemma iter_cm_step {C N: nat} : bound_reachable_n C N -> forall l r n, 
    let p := (Nat.iter n (CM1.step P) cm_start) in
    CM.value p <= G + C ->
    reachable_n (n * (step_time C N)) 
      ([§1] ++ l, [§0] ++ [§1] ++ (§0^(CM.value p - 1)) ++ r, '#?0)
      ([§1] ++ l, §0^(CM.value p) ++ [§1] ++ r, '#?(CM.state p)).
  Proof using capped_P.
    move=> HN l r n. elim: n l r => [l r _ _ | n] /=; first by apply: reach_refl.
    have := CM_facts.run_value_monotone P cm_start n.
    set p := (Nat.iter n (CM1.step P) cm_start) => Hp IH l r ?.
    rewrite /cm_start /= in Hp.
    have ? : CM.value p <= CM.value (CM1.step P p) by apply: CM_facts.step_value_monotone.
    have := IH l (§0^(CM.value (CM1.step P p) - CM.value p) ++ r) ltac:(lia).
    apply: (reachable_n_trans' (step_time C N)); 
      [by lia | by rewrite ?app_norm; do 6 f_equal; lia |].
    by have := do_cm_step HN l r p ltac:(lia).
  Qed.

  Lemma search_bound (C n: nat) : C <= CM.value (Nat.iter n (CM1.step P) cm_start) -> 
    {N | bound_reachable_n C N}.
  Proof using capped_P.
    elim: C.
    { 
      rewrite /bound_reachable_n. move=> _. exists 1.
      move=> m l r ?. have ->: m = 0 by lia.
      apply: (first_step bound_try_spec_1 r l);
        [by lia | by auto with M | by rewrite ?app_norm | by apply: reach_refl ].
    }
    move=> C IH HC. have [N HN] := IH ltac:(lia).

    (* time bound *)
    exists (n * step_time C N + increase_time C N + 3 * goto_time C N + 3).
    rewrite /bound_reachable_n. move=> [|[|m]] l r Hm.
    - apply: (first_step bound_try_spec_1 r l);
        [by lia | by auto with M | done | by apply: reach_refl ].
    - apply: (first_step bound_try_spec_01 r l);
        [by lia | by auto with M | done | by apply: reach_refl ].
    - apply: (first_step bound_try_spec_00 (§0^m ++ [§1] ++ r) l);
        [by lia | by auto with M | by rewrite ?app_norm | ].
      have ? : S m < CM.value (Nat.iter n (CM1.step P) cm_start) by lia.
      (* TODO have/lia regression; last ltac:(done) should be ltac:(lia) *)
      have [n' [?]] := transition_le_gt
        (fun n => CM.value (Nat.iter n (CM1.step P) cm_start)) (S m) 0 n ltac:(lia) ltac:(rewrite /cm_start /=; lia) ltac:(done).
      have := CM_facts.run_value_monotone P cm_start n'.
      set p' := (Nat.iter n' (CM1.step P) cm_start).
      have -> : Nat.iter (1 + n') (CM1.step P) cm_start = CM1.step P p' by done.
      move=> H1p' [? ?]. rewrite /cm_start /= in H1p'.
      have := iter_cm_step HN l (§0^(m - (CM.value p' - 1)) ++ [§1] ++ r) n'.
      rewrite -/p'. move /(_ ltac:(lia)).
      apply: (reachable_n_trans' (increase_time C N + 3 * goto_time C N + 2)); 
        [by nia | by rewrite ?app_norm; do 6 f_equal; lia |].

      have Hp' : CM.value p' < CM.value (CM.step P p') by lia.
      have [[p'j p'n] [/nth_error_Some_In_iP Hp'iP] /= Hp'n] := CM_facts.inc_value_mod Hp'.
      apply: (first_step (index_try_spec (CM.state p', (p'j, p'n))) 
        l (§0^(CM.value p' - 1) ++ [§1] ++ §0^(m - (CM.value p' - 1)) ++ [§1] ++ r));
          [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].

      rewrite ?app_norm. have ->: (1 + (CM.value p' - 1)) = CM.value p' by lia.
      apply: (first_goto_1 HN (increase_time C N + 2 * goto_time C N + 1)); 
        [ by eauto with M | by lia | by lia | ].
        
      set k := (m - (CM.value p' - 1)).
      have ?: (k + 1) * (1 + p'n) <= CM.value p'.
      { 
        suff: (CM.value (CM1.step P p') - CM.value p') * (1 + p'n) = CM.value p' by nia.
        suff: CM.value (CM1.step P p') = (CM.value p') * (p'n + 2) / (p'n + 1).
        { move=> ->. by have := divides_frac_diff Hp'n. }
        rewrite /CM1.step. have {1}->: CM1.value p' = S (CM1.value p' - 1) by lia.
        move: Hp'iP => /nth_error_Some_In_iP ->. by rewrite Hp'n.
      }
      have -> : CM.value p' = (k+1)*(1+p'n)+(CM.value p' - (k+1)*(1+p'n)) by lia.

      move: (Hp'iP) => /(fail_increase HN r (§0^(CM.value p' - (k + 1) * (1 + p'n)) ++ [§1] ++ l)) => /(_ k).
      have ? := iP_capped Hp'iP. have ? : 4 <= G by (rewrite /G; lia).
      have ? : (k + 1) * (2 + p'n) - (G + 1) <= C by lia.
      move /(_ ltac:(lia)).
      apply: (reachable_n_trans' (2 * goto_time C N + 1)); first by lia.
      { 
        rewrite ?app_norm.
        have ->: ((k + 1) * (1 + p'n) + (CM.value p' - (k + 1) * (1 + p'n))) = CM.value p' by lia.
        by rewrite Hp'n.
      }

      apply: (first_goto_1 HN (goto_time C N + 1)); [ by eauto with M | by lia | by lia |].

      apply: (first_step (increase_no_spec (CM.state p', (p'j, p'n)))
        (§0^(CM.value p' - (k + 1) * (1 + p'n)) ++ [§1] ++ l) (§0^((k + 1) * (1 + p'n) + k) ++ [§1] ++ r));
          [by lia | by auto with M | done | ].

      apply: (first_goto_1 HN 0); [by eauto with M | by move: ((k + 1) * (1 + p'n)); lia | by lia |].
      apply: reachable_n_refl'. rewrite ?app_norm ?nat_norm. do 4 f_equal. by lia.
  Qed.  

  Section Reflection.
  (* Assume that M is uniformly bounded by NM,
    show that P terminates from the starting configuration after at most NM steps *)
  Variable NM : nat. (* uniform bound for M *)
  Variable NM_spec : SM.bounded M NM.

  (* if stack machine is uniformly bounded, then counter machine halts *)
  Theorem bounded_M_to_terminating_P : CM.halting P (Nat.iter NM (CM.step P) cm_start).
  Proof using NM NM_spec capped_P.
    rewrite /CM.halting.
    move HNM: (Nat.iter NM (CM.step P) cm_start) => cm_end.
    have : CM.step P cm_end = cm_end \/ CM.step P cm_end <> cm_end by do 2 (decide equality).
    case; first done. move=> He. exfalso.
    have /CM_facts.acyclicity : not (CM.halting P (Nat.iter NM (CM.step P) cm_start)) by rewrite HNM.
    set f := (fun i : nat => Nat.iter i (CM1.step P) cm_start).
    rewrite seq_last map_app. move /(@NoDup_remove CM1.Config) => [+ _]. rewrite app_nil_r.
    have [L [H1L H2L]] := NM_spec ([§1], [§0] ++ [§1] ++ §0^(CM.value cm_end - 1), '#?0).
    set g : _ -> SM.Config := (fun X => ([§1], §0^(CM.value X) ++ [§1] ++ §0^(CM.value cm_end - (CM.value X)), '#? (CM.state X))).
    move /(NoDup_map (f := g)). apply: unnest.
    { move=> [p1 v1] [p2 v2]. rewrite /g /=. by move=> [] /zero_prefix_eq => -> ->. }
    set L' := (map g (map f (seq 0 (1 + NM)))). move=> HL'.
    have /(NoDup_incl_length HL') : incl L' L.
    { (* show that every encoded reachable in P configuration is reachable in M *)
      move=> x + /ltac:(apply: H1L). rewrite /L' in_map_iff.
      move=> [X] [<-]. rewrite in_map_iff. 
      move=> [i] [<-]. rewrite in_seq.
      move=> [_ ?]. rewrite /f /g.
      have [N HN] := search_bound (CM.value cm_end) NM ltac:(rewrite HNM; lia).
      have := CM_facts.run_value_monotone P cm_start i.
      set Y := (Nat.iter i (CM1.step P) cm_start).
      have ? : CM.value Y <= CM.value cm_end.
      { rewrite /Y -HNM. apply: CM_facts.value_monotone. by lia. }
      move=> H1Y. rewrite /cm_start /= in H1Y.
      have /= := iter_cm_step HN [] (§0^(CM.value cm_end - CM.value Y)) i.
      rewrite -/Y ?app_norm. move /(_ ltac:(lia)) /reachable_n_reachable.
      congr (SM.reachable). do 5 f_equal. by lia.
    }
    rewrite /L' ?map_length seq_length. by lia.
  Qed.

  End Reflection.

  Section Transport.
  (* Assume that P reaches a halting configuration from (0, 1) after NP steps, 
     show that M is uniformly bounded. *)

  Variable NP : nat. (* number of steps  *)
  Variable NP_spec : CM.halting P (Nat.iter NP (CM.step P) cm_start).
  Definition cm_end := Nat.iter NP (CM.step P) cm_start. (* final configuration *)
  Definition CP : nat := CM.value cm_end. (* final counter value *)
  
  Lemma bound_reachable_n_CP : {N | bound_reachable_n CP N}.
  Proof using capped_P. apply: (search_bound _ NP). rewrite /CP /cm_end. by lia. Qed.

  Definition TP : nat := sval (bound_reachable_n_CP). (* maximal time to reach bound *)
  Definition HTP : bound_reachable_n CP TP := svalP (bound_reachable_n_CP).

  Lemma CP_pos : 1 <= CP.
  Proof. have ->: 1 = CM.value cm_start by done. by apply: CM_facts.run_value_monotone. Qed.

  Lemma large_index_terminal {p i l r} : length P <= i -> terminal M (l, r, (basic_state (index p i))).
  Proof. move /not_in_iPI => Hi y /stepE [] > [] *; subst; by [| apply: Hi; eassumption]. Qed.

  Lemma large_increase_terminal {p i l r} : length P <= i -> terminal M (l, r, (basic_state (increase p i))).
  Proof. move /not_in_iPI => Hi y /stepE [] > [] *; subst; by [| apply: Hi; eassumption]. Qed.

  Lemma index_try_step_shape {y l r i} :
    SMX.step M (l, r, '#? i) y -> (l = [§1] ++ skipn 1 l) /\ (r = [§0] ++ skipn 1 r).
  Proof. by move /stepE => [] > [] *; subst. Qed.

  Lemma index_yes_step_shape {y l r i j n} :
    In (i, (j, n)) iP -> SMX.step M (l, r, '#+ i) y -> (r = [§1] ++ skipn 1 r) \/ (r = §0^(1+n) ++ skipn (n+1) r).
  Proof.
    move=> H1i /stepE [] > [] *; subst; try done.
    - by left.
    - right. move Hn': (n' in §0^(1 + n') ++ _) => n'. 
      have [_ <-] := in_iP_unique (n := n) (n' := n') ltac:(eassumption) ltac:(subst; eassumption).
      rewrite skipn_app repeat_length (_ : n + 1 - (1 + n) = 0); first by lia.
      by rewrite skipn_all2; first by (rewrite repeat_length; lia).
  Qed.

  Lemma index_no_step_shape {y l r i} :
    SMX.step M (l, r, '#-i) y -> (r = [§0] ++ skipn 1 r).
  Proof. by move /stepE => [] > [] *; subst. Qed.

  Lemma increase_try_step_shape {y l r i} :
    SMX.step M (l, r, '$?i) y -> (l = [§1] ++ [§0] ++ skipn 2 l) \/ (l = [§1] ++ [§1] ++ skipn 2 l).
  Proof. move=> /stepE [] > [] *; subst; try done; [by left | by right]. Qed.

  Lemma increase_yes_step_shape {y l r i} :
    SMX.step M (l, r, '$+i) y -> (l = [§1] ++ skipn 1 l).
  Proof. by move /stepE => [] > [] *; subst. Qed.

  Lemma increase_no_step_shape {y l r i} :
    SMX.step M (l, r, '$-i) y -> (l = [§1] ++ skipn 1 l).
  Proof. by move /stepE => [] > [] *; subst. Qed.

  Lemma bound_try_step_shape {y l r} :
    SMX.step M (l, r, '?|) y -> 
      ((l = [§1] ++ skipn 1 l) \/ (l = [§0] ++ [§1] ++ skipn 2 l) \/ (l = [§0] ++ [§0] ++ skipn 2 l)) /\ (r = [§1] ++ skipn 1 r).
  Proof. move /stepE => [] > [] *; subst; firstorder done. Qed.

  Local Definition maybe_reachable := maybe_reachable M.

  Lemma universal_maybe_reachable_terminal {x T} : (forall z, maybe_reachable T x z) -> 
    exists y, reachable_n T x y /\ terminal M y.
  Proof. 
    move=> /(_ ([], [], '?|)). case; last done.
    move=> ?. eexists. constructor; first by eassumption.
    by move=> ? /bound_try_step_shape [? ?].
  Qed.

  Lemma not_in_gotos_terminal l r n X Y : not (In (n, X, Y) gotos) -> terminal M (l, r, goto n X Y).
  Proof.
    move=> Hn y /stepE [] > [] *; subst; try done; apply: Hn; apply: in_combine_r; by eassumption.
  Qed.

  Lemma maybe_index_try_run l r z :
    maybe_reachable (NP * step_time CP TP) ([§1] ++ l, [§0] ++ [§1] ++ §0^(CP-1) ++ r, '#?0) z.
  Proof using NP_spec.
    right. have := iter_cm_step HTP l r NP. rewrite -/cm_end /= -/CP. move /(_ ltac:(lia)) => ?.
    eexists. constructor; first by eassumption.
    apply: large_index_terminal.
    suff : not (CM.state cm_end < length P) by lia.
    move /CM_facts.step_progress => /(_ CP_pos).
    move: (NP_spec). rewrite -/cm_end /CM.halting. move=> -> [|]; last by lia.
    move /(f_equal CM.state) => /=. by lia.
  Qed.

  Lemma maybe_goto_1_far {l r m n X Y z T} : (NP * step_time CP TP + 2) <= T -> G + (CP+1) <= m -> 
    maybe_reachable T (l, §0^m ++ r, goto n X Y) z.
  Proof using NP_spec.
    move=> ? ?. suff: maybe_reachable (NP * step_time CP TP + 2) (l, §0^(G + (CP+1)) ++ §0^(m-(G + (CP + 1))) ++ r, goto n X Y) z.
    { apply maybe_reachable_mon'; first by lia. rewrite ?app_norm. do 5 f_equal. by lia. }
    have := in_dec _ (n, X, Y) gotos. 
    move=> /(_ ltac:(do 4 (decide equality))) [/gotos_igotos [i ?]| ?]; first last.
      (* case (n, X, Y) not in gotos *)
    { apply: terminal_maybe_reachable. by apply: not_in_gotos_terminal. }
    (* case (n, X, Y) in gotos *)
    apply: (maybe_first_step (goto_spec_G (i, (n, X, Y))) l (§0^(CP + 1) ++ §0^(m-(G + (CP + 1))) ++ r));
      [by lia | by auto with M | by rewrite ?app_norm |].
    have ? := CP_pos.
    apply: (maybe_first_step bound_try_spec_00 (§0^(CP - 1 + (m - (G + (CP + 1)))) ++ r) (§0^i ++ [§1] ++ §0^(G - 2 - i) ++ l));
      [by lia | by auto with M | rewrite ?app_norm; do 4 f_equal; lia |].

    have := maybe_index_try_run ((§0^i ++ [§1] ++ §0^(G - 2 - i)) ++ l) (§0^(m - (G + (CP + 1))) ++ r) z.
    apply: maybe_reachable_mon'; [by lia | by rewrite ?app_norm].
  Qed.

  Definition maybe_goto_1_time := (goto_time CP TP + NP * step_time CP TP + 2).

  Lemma maybe_goto_1 l r n X Y m :
    maybe_reachable maybe_goto_1_time
      (l, §0^m ++ [§1] ++ r, goto n X Y) 
      ([§1] ++ r, §0^m ++ l, basic_state (if m mod (n+1) is 0 then X else Y)).
  Proof using NP_spec.
    rewrite /maybe_goto_1_time. have := in_dec _ (n, X, Y) gotos. 
    move=> /(_ ltac:(do 4 decide equality)) [| ?]; first last.
      (* case invalid goto instruction *)
    { apply: terminal_maybe_reachable. by apply: not_in_gotos_terminal. }
    have [? | ?]: m <= G + CP \/ G + CP < m by lia.
      (* case m is small enough *)
    { 
      move=> /gotos_igotos => [[i]] /(goto_1 HTP l r) => /(_ m ltac:(lia)) /reachable_n_maybe_reachable.
      apply: maybe_reachable_mon'; [by lia | done].
    }
    (* case m is too large *)
    move=> ?. apply: maybe_goto_1_far; by lia.
  Qed.

  Lemma maybe_first_goto_1 T l r T' n X Y c Z : T + maybe_goto_1_time <= T' ->
    maybe_reachable T ([§1] ++ r, §0^c ++ l, basic_state (if c mod (n+1) is 0 then X else Y)) Z ->
    maybe_reachable T' (l, §0^c ++ [§1] ++ r, goto n X Y) Z.
  Proof using NP_spec.
    move=> ? ?. have := maybe_goto_1 l r n X Y c.
    by (apply: (maybe_reachable_trans' T); first by lia).
  Qed.

  Definition maybe_index_try_stop_time := 
    (NP * step_time CP TP + 2*maybe_goto_1_time + 1 + ((G + CP + 2) * (2 * goto_time CP TP + 3))).

  Lemma maybe_index_try_stop l m z T : maybe_index_try_stop_time <= T ->
    maybe_reachable T ([§1] ++ l, §0^1 ++ [§1] ++ §0^m, '#?0) z.
  Proof using NP_spec.
    move /maybe_reachable_mon'. apply; first by reflexivity. rewrite /maybe_index_try_stop_time.
    have [? | Hm]: CP - 1 <= m \/ m < CP - 1 by lia.
    { 
      have := maybe_index_try_run l (§0^(m - (CP - 1))) z. 
      apply: maybe_reachable_mon'; [by nia | by rewrite ?app_norm; do 6 f_equal; lia ].
    }
    
    set T' := ((G + CP + 2) * (2 * goto_time CP TP + 3)).
    have [n [?]] := transition_le_gt 
      (fun n => CM.value (Nat.iter n (CM1.step P) cm_start)) (m + 1) 0 NP 
      ltac:(lia) ltac:(rewrite /cm_start /=; lia) ltac:(rewrite /cm_end -/CP; lia).

    have := CM_facts.run_value_monotone P cm_start n.
    set p := (Nat.iter n (CM1.step P) cm_start).
    have -> : Nat.iter (1 + n) (CM1.step P) cm_start = CM1.step P p by done.
    move=> H1p [? ?]. rewrite /cm_start /= in H1p.

    have := iter_cm_step HTP l (§0^(m - (CM.value p - 1))) n.
    rewrite -/p. move=> /(_ ltac:(lia)) /reachable_n_maybe_reachable.
    apply: (maybe_reachable_trans' (2*maybe_goto_1_time + 1 + T')); 
      [ by nia | rewrite ?app_norm; do 6 f_equal; by lia | ].
    
    have Hp : CM.value p < CM.value (CM.step P p) by lia.
    have [[pj pn] [/nth_error_Some_In_iP HpiP] /= Hpn] := CM_facts.inc_value_mod Hp.
    apply: (maybe_first_step (index_try_spec (CM.state p, (pj, pn)))
      l (§0^(CM.value p - 1) ++ [§1] ++ §0^(m - (CM.value p - 1))));
        [by nia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].

    rewrite ?app_norm. have ->: (1 + (CM.value p - 1)) = CM.value p by lia.
    apply: (maybe_first_goto_1 (maybe_goto_1_time + T')); [by lia | rewrite Hpn].

    set k := (m - (CM.value p - 1)).
    have ?: (k + 1) * (1 + pn) <= CM.value p.
    { 
      suff: (CM.value (CM1.step P p) - CM.value p) * (1 + pn) = CM.value p by nia.
      suff: CM.value (CM1.step P p) = (CM.value p) * (pn + 2) / (pn + 1).
      { move=> ->. by have := divides_frac_diff Hpn. }
      rewrite /CM1.step. have {1}->: CM1.value p = S (CM1.value p - 1) by lia.
      move: HpiP => /nth_error_Some_In_iP ->. by rewrite Hpn.
    }
    have -> : CM.value p = (k+1)*(1+pn)+(CM.value p - (k+1)*(1+pn)) by lia.

    have := do_increase HTP [] (§0^((1 + pn) + (CM.value p - (k + 1) * (1 + pn))) ++ [§1] ++ l) k 0 HpiP ltac:(lia).
    move /reachable_n_maybe_reachable. apply: (maybe_reachable_trans' (maybe_goto_1_time + goto_time CP TP + 1)); first by nia.
    { rewrite ?app_norm. do 4 f_equal. by lia. }

    apply: (maybe_first_step (index_yes_spec_n1 (CM1.state p, (pj, pn))) (§0^(k * (2 + pn)) ++ [§1]) (§0^(CM.value p - (k + 1) * (1 + pn)) ++ [§1] ++ l));
      [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
    
    rewrite ?app_norm. apply: (maybe_first_goto_1 0); first by lia.
    rewrite ?app_norm. right. eexists. constructor; first by apply: reach_refl.
    by move=> ? /increase_try_step_shape [|].
  Qed.

  Lemma maybe_goto_1_futile {T l n X Y m z} :    
    maybe_index_try_stop_time + 2 <= T -> maybe_reachable T (l, §0^m, goto n X Y) z.
  Proof using NP_spec.
    move=> ?. suff: maybe_reachable (maybe_index_try_stop_time + 2) (l, §0^m, goto n X Y) z 
      by apply: maybe_reachable_mon'.
    rewrite /maybe_index_try_stop_time.
    have /(_ ltac:(do 4 decide equality)) [HnXY | /not_in_gotos_terminal ?] := 
      in_dec _ (n, X, Y) gotos; last by apply: terminal_maybe_reachable.
    have [? | ?]: G+CP+1 <= m \/ m <= G+CP by lia.
      (* case m too large *)
    { have := @maybe_goto_1_far l [] m. rewrite ?app_norm. apply; by lia. }
    have [? | ?]: m < G \/ G <= m by lia.
      (* case m is too small *)
    {  
      right. exists (l, §0^m, goto n X Y). constructor; first by apply: reach_refl.
      move=> y /stepE [] > []; try done.
      - move=> ? /(f_equal (@length Symbol)). rewrite ?app_length ?repeat_length. by lia.
      - move=> ? Hm. exfalso. have : not (In §1 (§0^m)) by move /(@repeat_spec Symbol).
        apply. rewrite Hm ?in_app_iff. clear. by firstorder done.
    }
    (* case m is large enough to try bound search *) 
    move: (HnXY) => /gotos_igotos => [[i ?]].

    apply: (maybe_first_step (goto_spec_G (i, (n, X, Y))) l (§0^(m - G)));
      [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].

    have [? | ?] : m - G < 2 \/ 2 <= m - G by lia.
      (* case m is too small to continue *)
    { 
      right. eexists. constructor; first by apply: reach_refl.
      move=> ? /bound_try_step_shape. have : m - G = 0 \/ m - G = 1 by lia.
      move=> [-> | ->]; clear; by firstorder done.
    }
    (* case m is large enough to start bound search *)  
    apply: (maybe_first_step bound_try_spec_00 (§0^(m - G - 2)) (§0^i ++ [§1] ++ §0^(G - 2 - i) ++ l));
      [by lia | by auto with M | by rewrite ?app_norm; do 3 f_equal; lia |].
    rewrite ?app_norm. apply: maybe_index_try_stop. rewrite /maybe_index_try_stop_time. by lia.
  Qed.

  Arguments maybe_first_goto_1 T {l r T' n X Y c Z}. 

  Definition maybe_increase_time := ((G + CP + 2) * (2 * maybe_goto_1_time + 3)).

  Lemma maybe_increase l r i j n k m : In (i, (j, n)) iP -> 
    maybe_reachable maybe_increase_time
      (§0^m ++ [§1] ++ §0^k ++ l, §0^(k * (1+n)) ++ r, '#+i) 
      (§0^(m + k * (2+n)) ++ [§1] ++ l, r, '#+i).
  Proof using NP_spec.
    rewrite /maybe_increase_time. move=> Hijn. move: l r k m.
    have H : forall k m l r, maybe_reachable ((k+1)*(2 * maybe_goto_1_time + 3))
      (§0^m ++ [§1] ++ §0^k ++ l, §0^(k * (1+n)) ++ r, '#+i) 
      (§0^(m + k * (2+n)) ++ [§1] ++ l, r, '#+i).
    {
      elim.
        (* case k = 0 *)
      { move=> m l r. rewrite ?app_norm ?nat_norm. by apply: maybe_reachable_refl'. }
      (* case k > 0 *)
      move=> k IH m l r. have ? := iP_capped Hijn.
      pose N' := (k+1)*(2 * maybe_goto_1_time + 3).
      apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^m ++ [§1] ++ §0^(1+k) ++ l) (§0^(k * (1 + n)) ++ r));
        [by lia | by auto with M | by rewrite ?app_norm |].

      rewrite ?app_norm. apply: (maybe_first_goto_1 (N' + maybe_goto_1_time + 2)); first by lia.
      apply: (maybe_first_step (increase_try_spec_0 (i, (j, n))) (§0^k ++ l) (§0^(n + m) ++ [§1] ++ §0^(k * (1 + n)) ++ r));
        [by lia | by auto with M | by rewrite ?app_norm |].

      rewrite ?app_norm. apply: (maybe_first_goto_1 (N' + 1)); first by lia.
      apply: (maybe_first_step (increase_yes_spec (i, (j, n))) (§0^(k * (1 + n)) ++ r) (§0^(1 + (n + m)) ++ [§1] ++ §0^k ++ l));
        [by lia | by auto with M | by rewrite ?app_norm |].

      have := IH (m + n + 2) l r. apply: maybe_reachable_mon'; first by lia.
      rewrite ?app_norm. by do 5 f_equal; lia.
    }
    move=> l r k m. have [? | ?] : k <= G + CP \/ G + CP < k by lia.
    { have := H k m l r. by apply: maybe_reachable_mon'; first by nia. }
    pose k' := G + CP. have := H k' m (§0^(k-k') ++ l) (§0^((k-k') * (1 + n)) ++ r).
    apply: (maybe_reachable_trans' (maybe_goto_1_time + 1)); first by lia.
    { rewrite ?app_norm. (do 4 f_equal); last by lia. do 2 f_equal. by lia. }
    apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n)))
      (§0^(m + k' * (2 + n)) ++ [§1] ++ §0^(k - k') ++ l) (§0^((k - k' - 1) * (1 + n)) ++ r));
      [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; nia | ].
    rewrite ?app_norm /k'. have ? := CP_pos.
    rewrite /maybe_goto_1_time. apply: maybe_goto_1_far; by lia.
  Qed.

  Arguments maybe_increase l r {i j n} k m.

  Lemma maybe_increase_next l r i j n c k m : In (i, (j, n)) iP -> c / (1+n) <= k ->
    maybe_reachable (maybe_increase_time+1)
      (§0^m ++ [§1] ++ §0^k ++ l, §0^c ++ [§1] ++ r, '#+i) 
      ([§1] ++ r, §0^(m + c + (c / (1+n)) + (c mod (1+n))) ++ [§1] ++ §0^(k - (c / (1+n))) ++ l, '#?j).
  Proof using NP_spec.
    have := Nat.div_mod c (1+n) ltac:(lia).
    move: (c / (1+n)) => k'.
    have ->: (1 + n) * k' = k' * (1 + n) by lia.
    move=> ? Hijn ?.
    have := maybe_increase (§0^(k-k') ++ l) (§0^(c mod (1 + n)) ++ [§1] ++ r) k' m Hijn.
    apply: (maybe_reachable_trans' 1); first by lia.
    { rewrite ?app_norm. do 4 f_equal; last by lia. do 2 f_equal. by lia. }
    have ? := Nat.mod_upper_bound c (1+n) ltac:(lia).
    have [Hc | Hc]: c mod (1 + n) = 0 \/ c mod (1 + n) = 1 + (c mod (1 + n) - 1) by lia.
      (* case 1+n divides c *)
    {
      rewrite Hc.
      apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) (§0^(m + k' * (2 + n)) ++ [§1] ++ §0^(k - k') ++ l) r);
        [ by lia | by auto with M | done | ].
      apply: maybe_reachable_refl'. rewrite ?nat_norm ?app_norm. do 4 f_equal. by lia.
    }
    (* case 1+n does not divide c *)
    rewrite Hc. apply: terminal_maybe_reachable.
    move=> ? /(index_yes_step_shape Hijn) [| /zero_prefix_lt]; by [| lia].
  Qed.

  Lemma maybe_increase_stop r i j n c k m z : In (i, (j, n)) iP -> k < c / (1+n) ->
    maybe_reachable (maybe_increase_time+ maybe_goto_1_time + 1) 
      (§0^m ++ [§1] ++ §0^k, §0^c ++ [§1] ++ r, '#+i) z.
  Proof using NP_spec.
    have := Nat.div_mod c (1+n) ltac:(lia).
    move: (c / (1 + n)) => k'. move: (c mod (1 + n)) => k'' -> Hijn ?.
    have := maybe_increase [] (§0^((1 + n) * (k'-k) + k'') ++ [§1] ++ r) k m Hijn.
    apply: (maybe_reachable_trans' (maybe_goto_1_time + 1)); first by lia.
    { rewrite ?app_norm. do 4 f_equal. by lia. }
    move: ((m + k * (2 + n))) => {}m.
    apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) 
      (§0^m ++ [§1]) (§0^((1 + n) * (k' - k - 1) + k'') ++ [§1] ++ r));
        [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; nia |].
    rewrite ?app_norm. apply: (maybe_first_goto_1 0); first by lia.
    by apply: terminal_maybe_reachable => ? /increase_try_step_shape [|].
  Qed.
  
  Lemma maybe_increase_fail l r i j n c k m : In (i, (j, n)) iP -> k < c / (1+n) ->
    maybe_reachable (maybe_increase_time + 3*maybe_goto_1_time + 3) 
      (§0^m ++ [§1] ++ §0^k ++ [§1] ++ l, §0^c ++ [§1] ++ r, '#+i) 
      ([§1] ++ r,  §0^(c+m+k+1) ++ [§1] ++ l, '+|).
  Proof using NP_spec.
    have := Nat.div_mod c (1+n) ltac:(lia).
    move: (c / (1 + n)) => k'. move: (c mod (1 + n)) => k'' -> Hijn ?.
    have := maybe_increase ([§1] ++ l) (§0^((1 + n) * (k'-k) + k'') ++ [§1] ++ r) k m Hijn.
    apply: (maybe_reachable_trans' (3*maybe_goto_1_time + 3)); first by lia.
    { rewrite ?app_norm. do 4 f_equal. by lia. }
    apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) 
      (§0^((m + k * (2 + n))) ++ [§1] ++ [§1] ++ l) (§0^((1 + n) * (k' - k - 1) + k'') ++ [§1] ++ r));
        [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; nia |].
    rewrite ?app_norm. apply: (maybe_first_goto_1 (2*maybe_goto_1_time + 2)); first by lia.
    apply: (maybe_first_step (increase_try_spec_1 (i, (j, n))));
      [by lia | by auto with M | by rewrite ?app_norm; reflexivity |].
    rewrite ?app_norm. apply: (maybe_first_goto_1 (maybe_goto_1_time + 1)); first by lia.
    apply: (maybe_first_step (increase_no_spec (i, (j, n))));
      [ by lia | by auto with M | by rewrite ?app_norm; reflexivity |].
    rewrite ?app_norm. apply: (maybe_first_goto_1 0); first by lia.
    apply: maybe_reachable_refl'. rewrite ?app_norm. do 4 f_equal. by nia.
  Qed.

  Definition maybe_index_try_step_time := 2*maybe_goto_1_time + maybe_increase_time +2.

  Lemma maybe_index_try_step l r p : 
    maybe_reachable maybe_index_try_step_time
      ([§1] ++ l, §0^(CM.value p) ++ [§1] ++ §0^(CM.value (CM1.step P p) - CM.value p) ++ r, '#?(CM.state p))
      ([§1] ++ l, §0^(CM.value (CM1.step P p)) ++ [§1] ++ r, '#?(CM.state (CM1.step P p))).
  Proof using NP_spec.
    rewrite /maybe_index_try_step_time. move: p => [i [|c]] /=.
      (* case c = 0 *)
    { by apply: maybe_reachable_refl'. }
    (* case c > 0 *)
    move H: (nth_error P i) => oi. case: oi H; first last.
    { move=> _ /=. rewrite ?nat_norm ?app_norm. by apply: maybe_reachable_refl'. }
    move=> [j n] /nth_error_Some_In_iP /=.
    move Hm: (S c mod (n + 1)) => m. move: m Hm => [|m] Hcn /= Hijn.
    (* case n+1 divides c *)
    - have := mod_frac_lt Hcn.
      move Hd: (S c * (n + 2) / (n + 1)) => d Hcd.

      apply: (maybe_first_step (index_try_spec (i, (j, n))) l (§0^c ++ [§1] ++ §0^(d - S c) ++ r)); 
        [ by lia | by auto with M | by rewrite ?app_norm | ].

      rewrite ?app_norm. apply: (maybe_first_goto_1 (maybe_goto_1_time + maybe_increase_time + 1)); first by lia.
      rewrite Hcn.
      have ? : (d - S c) * (1 + n) = S c.
      { rewrite -Hd. by apply: divides_frac_diff. }
      have := maybe_increase r ([§1] ++ l) (d - S c) 0 Hijn.

      apply: (maybe_reachable_trans' (maybe_goto_1_time + 1)); first by lia.
      { rewrite ?app_norm. do 4 f_equal. by lia. }

      apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))));
        [by lia | by auto with M | by rewrite ?app_norm; reflexivity | ].
      apply: maybe_reachable_refl'. rewrite ?app_norm. do 4 f_equal. by lia.
    (* case n+1 does not divide c *)
    - apply: (maybe_first_step (index_try_spec (i, (j, n))) l (§0^c ++ [§1] ++ r));
        [by lia | by auto with M | by rewrite ?app_norm ?nat_norm | ].
      rewrite ?app_norm. apply: (maybe_first_goto_1 (maybe_goto_1_time + 1)); first by lia.
      rewrite Hcn.

      apply: (maybe_first_step (index_no_spec (i, (j, n))) ([§1] ++ r) (§0^c ++ [§1] ++ l));
        [ by lia | by auto with M | done |].

      rewrite ?app_norm. apply: (maybe_first_goto_1 0); [by lia | by apply: maybe_reachable_refl'].
  Qed.

  Definition maybe_index_try_futile_time := maybe_index_try_stop_time + 3.

  Lemma maybe_index_try_futile l m i z : 
    maybe_reachable maybe_index_try_futile_time (l, §0^m, '#?i) z.
  Proof using NP_spec.
    rewrite /maybe_index_try_futile_time.
    move: l => [|a l].
      (* case l is empty *)
    { by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?]. }
    case: a.
      (* case l starts with 0 *)
    { by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?]. }
    have [-> | ?] : m = 0 \/ 1 <= m by lia.
      (* case m is 0 *)
    { by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?]. }
    (* case m is non-zero *)
    have [? | /in_iPI [j [n Hijn]]]: length P <= i \/ i < length P by lia.
      (* case i is not a valid instruction index *)
    { apply: terminal_maybe_reachable. by apply: large_index_terminal. }
    (* case i is a valid instruction index *)
    apply: (maybe_first_step (index_try_spec (i, (j, n))) l (§0^(m-1)));
      [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia | ].
    rewrite ?app_norm. apply: maybe_goto_1_futile. by lia.
  Qed.

  Definition maybe_bounded_try_time := TP + maybe_index_try_stop_time + 1.

  Lemma maybe_bounded_try l r : maybe_reachable maybe_bounded_try_time (r, l, '?|) (l, r, '+|).
  Proof using NP_spec.
    rewrite /maybe_bounded_try_time.
    move: l => [|a l]. 
      (* case l is empty *)
    { right. eexists. constructor; first by apply: reach_refl.
      by move=> ? /bound_try_step_shape [? ?]. }
    (* case l contains at least one symbol *)
    case: a.
      (* case l starts with 0 *)
    { right. eexists. constructor; first by apply: reach_refl.
      by move=> ? /bound_try_step_shape [? ?]. }
    (* case l starts with 1 *)
    move: r => [|b r].
      (* case r is empty *)
    { right. eexists. constructor; first by apply: reach_refl.
      by move=> ? /bound_try_step_shape [[|[|]] ?]. }
    (* case r has at least one symbol *)
    case: b.
      (* case r starts with 0 *)
    {
      move: r=> [|b r].
        (* case r is [0] *)
      { right. eexists. constructor; first by apply: reach_refl.
        by move=> ? /bound_try_step_shape [[|[|]] ?]. }
      (* case r starts with 0; b *)
      case: b.
      { (* case r starts with 0; 0  - search for bound *)
        have [[m ->]|] := list_symbol_shape r.
          (* case r has no 1 *)
        { apply: (maybe_first_step bound_try_spec_00 (§0^m) l); 
            [ by lia | by auto with M | by rewrite ?app_norm | ].
          rewrite ?app_norm. apply: maybe_index_try_stop. by lia. }
        (* case r has an 1 *)
        move=> [m [+ ->]] => {}r.
        have [| ?]: m + 2 <= CP \/ CP < m + 2 by lia.
          (* case m is small *)
        { move /(HTP (m+2) l r) => + /ltac:(left).
          apply: reachable_n_mon'; first by lia.
            rewrite ?app_norm. do 5 f_equal; by lia. }
        (* case m is large enough *)
        apply: (maybe_first_step bound_try_spec_00 (§0^m ++ [§1] ++ r) l); 
          [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia | ].
        have := maybe_index_try_run l (§0^(m - (CP - 1)) ++ [§1] ++ r) (§1 :: l, §0 :: §0 :: §0^m ++ [§1] ++ r, '+|).
        apply: maybe_reachable_mon'; first by (rewrite /maybe_index_try_stop_time; nia).
        rewrite ?app_norm. do 7 f_equal. by lia.
      }
      (* case r starts with 0; 1 *)
      apply: (maybe_first_step bound_try_spec_01 r l);
        [ by lia | by auto with M | by rewrite ?app_norm |].
      apply: maybe_reachable_refl'. by rewrite ?app_norm.
    }
    (* case r starts with 1 *)
    apply: (maybe_first_step bound_try_spec_1 r l);
      [ by lia | by auto with M | by rewrite ?app_norm |].
    apply: maybe_reachable_refl'. by rewrite ?app_norm.
  Qed.

  Lemma maybe_index_yes_near_futile l m i j n z : In (i, (j, n)) iP -> m <= n ->
    maybe_reachable 0 (l, §0^m, '#+i) z.
  Proof.
    move=> Hijn ?. apply: terminal_maybe_reachable.
    move=> ? /(index_yes_step_shape Hijn). case; first by case: (m).
    move /(f_equal (@length Symbol)). rewrite ?app_length ?repeat_length. by lia.
  Qed.

  Definition maybe_index_yes_futile_time := 2*maybe_goto_1_time + maybe_increase_time + maybe_index_try_stop_time + 5.

  Lemma maybe_index_yes_futile l m i z : 
    maybe_reachable maybe_index_yes_futile_time (l, §0^m, '#+i) z.
  Proof using NP_spec.
    rewrite /maybe_index_yes_futile_time.
    have [? | /in_iPI [j [n Hijn]]] : length P <= i \/ i < length P by lia.
      (* case i is not a valid instruction index *)
    { apply: terminal_maybe_reachable. by apply: large_index_terminal. }
    (* case i is a valid instruction index *)
    have [? | ?] : m <= n \/ n < m by lia.
      (* case m is too small *)
    { apply: (maybe_reachable_mon' (n := 0)); [by lia | by reflexivity |].
      apply: maybe_index_yes_near_futile; by eassumption. }
    (* case m is large enough *)
    have [[m' ->]|]:= list_symbol_shape l.
      (* case l contains only 0s *)
    { apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^m') (§0^(m-(n+1))));
        [ by lia | by auto with M | by rewrite ?app_norm; do 5 f_equal; lia |].
        rewrite ?app_norm. apply: maybe_goto_1_futile. by lia. }
    (* case l contains at least one 1 *)
    move=> [k1 [+ ->]] => {}l.
    have [[k2 ->]|] := list_symbol_shape l.
      (* case l is 0s; 1; 0s *)
    { 
      have [| ?]: m / (1+n) <= k2 \/ k2 < m / (1+n) by lia.
        (* case k2 is large enough *)
      { 
        have := Nat.div_mod m (1+n) ltac:(lia).
        move Hk: (m / (1+n)) => k Hm ?.
        have := maybe_increase (§0^(k2-k)) (§0^(m mod (1 + n))) k k1 Hijn.
        apply: (maybe_reachable_trans' 0); first by lia.
        { rewrite ?app_norm. do 5 f_equal; by lia. }

        apply: (maybe_reachable_mon' (n := 0)); [by lia | by reflexivity |].
        move: (Hijn) => /maybe_index_yes_near_futile. apply.
        have := Nat.mod_upper_bound m (1+n) ltac:(lia). by lia.
      }
      (* case k2 is too small *)
      have := maybe_increase [] (§0^(m - k2 * (1+n))) k2 k1 Hijn.
      apply: (maybe_reachable_trans' (maybe_goto_1_time + 1)); first by lia.
      { rewrite ?app_norm. do 5 f_equal.
        have ? := div_mul_le m (1+n) ltac:(lia). by nia. }
      move: (m - k2 * (1 + n)). move: (k1 + k2 * (2 + n)) => k1' m'.
      have [? | ?]: m' <= n \/ n < m' by lia.
        (* case m' is too small *)
      { apply: (maybe_reachable_mon' (n := 0)); [by lia | by reflexivity |].
        apply: maybe_index_yes_near_futile; by eassumption. }
      (* case m' is large enough *)
      apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^k1' ++ [§1]) (§0^(m' - (n+1))));
        [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
  
      rewrite ?app_norm. apply: (maybe_first_goto_1 0); first by lia.
      by apply: terminal_maybe_reachable => ? /increase_try_step_shape [|].
    }
    (* case l is 0s; 1; 0s; 1; ... *)
    move=> [k2 [+ ->]] => {}l.
    have [| ?] : m / (1+n) <= k2 \/ k2 < m / (1+n) by lia.
      (* case k2 is large enough *)
    {
      have := Nat.div_mod m (1+n) ltac:(lia).
      move Hk: (m / (1+n)) => k Hm ?.
      have := maybe_increase (§0^(k2-k) ++ [§1] ++ l) (§0^(m mod (1 + n))) k k1 Hijn.
      apply: (maybe_reachable_trans' 0); first by lia.
      { rewrite ?app_norm. do 5 f_equal; last by lia. f_equal. by lia. }
      apply: (maybe_reachable_mon' (n := 0)); first by lia.
      { by reflexivity. }
      move: (Hijn) => /maybe_index_yes_near_futile. apply.
      have := Nat.mod_upper_bound m (1+n) ltac:(lia). by lia.
    }
    (* case k2 is small *)
    have := maybe_increase ([§1] ++ l) (§0^(m - k2 * (1+n))) k2 k1 Hijn.
    apply: (maybe_reachable_trans' (2*maybe_goto_1_time + maybe_index_try_stop_time + 5)); first by lia.
    { rewrite ?app_norm. do 5 f_equal. have ? := div_mul_le m (1+n) ltac:(lia). by nia. }
    move: (m - k2 * (1 + n)). move: (k1 + k2 * (2 + n)) => k1' m'.
    have [? | ?]: m' <= n \/ n < m' by lia.
      (* case m' is too small *)
    { apply: (maybe_reachable_mon' (n := 0)); [by lia | by reflexivity |].
      apply: maybe_index_yes_near_futile; by eassumption. }
    (* case m' is large enough *)
    apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^k1' ++ [§1] ++ [§1] ++ l) (§0^(m' - (n+1))));
      [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].

    rewrite ?app_norm. apply: (maybe_first_goto_1 (maybe_goto_1_time + maybe_index_try_stop_time + 4)); first by lia.
    apply: (maybe_first_step (increase_try_spec_1 (i, (j, n))) l (§0^(n + k1') ++ [§1] ++ §0^(m' - (n + 1))));
      [ by lia | by auto with M | by rewrite ?app_norm |].

    rewrite ?app_norm. apply: (maybe_first_goto_1 (maybe_index_try_stop_time + 3)); first by lia.
    apply: (maybe_first_step (increase_no_spec (i, (j, n))) (§0^(m' - (n + 1))) (§0^(1 + (n + k1')) ++ [§1] ++ l));
      [ by lia | by auto with M | by rewrite ?app_norm |].
    rewrite ?app_norm. apply: maybe_goto_1_futile. by lia.
  Qed.

  (* Grow Lemmas: lX0^mr ->> lX0^(m+1)r *)

  Lemma maybe_bounded_yes_grow l r m : exists '(l', r', n, X, Y), 
    maybe_reachable 1 (l, §0^m ++ r, '+|) (l', §0^(m+1) ++ r', goto n X Y).
  Proof using capped_P.
    have := Exists_dec (fun '(i, (n, X, Y)) => l = ([§1] ++ §0^i ++ [§1] ++ §0^(G-2-i)) ++ skipn G l) igotos. 
    case.
    { move=> [i] [[n X] Y]. by do 2 (decide equality). }
    (* can execute bound op *)
    - rewrite Exists_exists. move=> [[i] [[n X] Y]] [Hi ->].
      exists ((§0^(n + 1) ++ skipn G l), (§0^(G - (n + 2)) ++ r), n, X, Y).

      apply: (maybe_first_step (bound_yes_spec (i, (n, X, Y))) (skipn G l) (§0^m ++ r));
        [by lia | by auto with M | done |].
      apply: maybe_reachable_refl'. have ? := igotos_capped Hi.
      rewrite /G ?app_norm /gotos ?app_length /=. do 4 f_equal. by lia.
    (* cannot execute bound op *)
    - move=> H. exists ([], [], 0, +|, +|). apply: terminal_maybe_reachable.
      move=> y /stepE [] > [] *; subst; try done.
      apply: H. apply /Exists_exists. eexists. constructor; first by eassumption.
      rewrite /= ?app_norm. do 4 f_equal. rewrite ?app_assoc skipn_app.
      have ? := in_igotos_lt ltac:(eassumption).
      set s := (skipn G _). have -> : s = [].
      { rewrite /s skipn_all2; last done. rewrite ?app_length ?repeat_length /= /G. by lia. }
      rewrite ?app_length ?repeat_length /= /G.
      set k := (k in skipn k _). have -> : k = 0 by lia. done.
  Qed.

  Definition maybe_increase_no_grow_time := maybe_goto_1_time + maybe_index_try_stop_time + 3.

  Lemma maybe_increase_no_grow l r m i : exists '(l', r', n, X, Y), 
    maybe_reachable maybe_increase_no_grow_time (l, §0^m ++ r, '$-i) (l', §0^(m+1) ++ r', goto n X Y).
  Proof using NP_spec.
    pose dummy := ([§0], [§0], 0, +|, +|). rewrite /maybe_increase_no_grow_time.
    have [? | /in_iPI [j [n Hjn]]]: length P <= i \/ i < length P by lia.
      (* case i is not a valid instruction index *)
    { exists dummy. apply: terminal_maybe_reachable. by apply: large_increase_terminal. }
    (* case i is a valid instruction index *)
    move: l => [|a l].
      (* case l is empty *)
    { exists dummy. by apply: terminal_maybe_reachable => ? /increase_no_step_shape. }
    case: a.
      (* case l starts with 0 *)
    { exists dummy. by apply: terminal_maybe_reachable => ? /increase_no_step_shape. }
    (* case l starts with 1 *)
    have [[m' ->]|] := list_symbol_shape l.
      (* case l is 1; 0; 0; 0; ... *)
    { exists dummy.
      apply: (maybe_first_step (increase_no_spec (i, (j, n))) (§0^m') (§0^m ++ r));
        [ by lia | by auto with M | by rewrite ?app_norm | ].
      rewrite ?app_norm. apply: maybe_goto_1_futile. by lia. }
    (* case: l contains a second 1 *)
    move=> [m' [+ ->]] => {}l.
    have [e He] := maybe_bounded_yes_grow ([§1] ++ l) (§0^(m'+1) ++ r) m.
    exists e. move: e He => [[[[l' r'] n'] X'] Y'] He.
    apply: (maybe_first_step (increase_no_spec (i, (j, n))) (§0^m' ++ [§1] ++ l) (§0^m ++ r));
      [by lia | by auto with M | by rewrite ?app_norm | ].
    rewrite ?app_norm. apply: (maybe_first_goto_1 1); first by lia.
    move: He. apply: maybe_reachable_mon'; first by lia.
    rewrite ?app_norm. do 5 f_equal. by lia.
  Qed.

  Definition maybe_index_yes_grow_time := maybe_index_yes_futile_time + maybe_increase_time + 3 * maybe_goto_1_time + maybe_index_try_stop_time + 4.
  
  Lemma maybe_index_yes_grow l r m i: exists '(l', r', n, X, Y), 
    maybe_reachable maybe_index_yes_grow_time (l, §0^m ++ r, '#+i) (l', §0^(m+1) ++ r', goto n X Y).
  Proof using NP_spec.
    rewrite /maybe_index_yes_grow_time. pose dummy := ([§0], [§0], 0, +|, +|).
    have [[n ->] | ] := list_symbol_shape r.
      (* case r contains only 0s *)
    { exists dummy. 
      apply: (maybe_reachable_mon' (n := maybe_index_yes_futile_time)); 
        [ by lia | by rewrite ?app_norm; reflexivity | by apply: maybe_index_yes_futile]. }
    move=> [m' [+ ->]] => {}r.
    have [Hi | /in_iPI [j [n Hijn]]]: length P <= i \/ i < length P by lia.
      (* case i is not a valid instruction index *)
    { exists dummy. apply: terminal_maybe_reachable. by apply: large_index_terminal. }
    (* case i is a valid instruction index *)
    rewrite ?app_norm.
    suff: exists '(l', r', n, X, Y), maybe_reachable maybe_index_yes_grow_time
      (l, §0^(m+m') ++ [§1] ++ r, '#+i) (l', §0^((m+m')+1) ++ r', goto n X Y).
    {
      move=> [[[[[l' r'] n'] X'] Y'] H]. exists (l', §0^m' ++ r', n', X', Y').
      move: H. apply: maybe_reachable_mon'; first by (rewrite /maybe_index_yes_grow_time; lia).
      rewrite ?app_norm. do 5 f_equal. by lia.
    }
    move: (m + m') => {}m {m'}. rewrite /maybe_index_yes_grow_time.
    move: m => [|m].
      (* case m = 0 *)
    { 
      move: l => [|a l].
        (* case l is empty *)
      { exists dummy. apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) [] r);
          [by lia | by auto with M | done |].
        by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?]. }
      case: a.
        (* case l starts with 0 *)
      { 
        have [/in_iPI [j'] [n'] Hjj'n' | Hj] : j < length P \/ length P <= j by lia.
          (* case j is a valid instruction index *)
        { exists (([§1] ++ r), l, n', (#+j), (#-j)).
          apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) ([§0] ++ l) r);
            [by lia | by auto with M | done |].
          by apply: (maybe_first_step (index_try_spec (j, (j', n'))) r l);
            [by lia | by auto with M | done | by apply: maybe_reachable_refl']. }
        (* case j is not a valid instruction index *)
        exists dummy. apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) ([§0] ++ l) r);
          [by lia | by auto with M | done |].
        apply: terminal_maybe_reachable. by apply: large_index_terminal.
      }
      (* case l starts with 1 *)
      exists dummy. apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) ([§1] ++ l) r);
        [by lia | by auto with M | done |].
      apply: terminal_maybe_reachable. by move=> ? /index_try_step_shape [? ?].
    }
    (* case m > 0 *)
    have [[k ->] |] := list_symbol_shape l.
      (* case l contains only 0s *)
    { 
      exists dummy.
      have [? | ?]: S m < n + 1 \/ n + 1 <= S m by lia.
      { apply: terminal_maybe_reachable=> ? /(index_yes_step_shape Hijn) [|/zero_prefix_lt]; [ done | by lia]. }
      apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^k) (§0^(m-n) ++ [§1] ++ r));
        [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia | ].
      rewrite ?app_norm. apply: maybe_goto_1_futile. by lia.
    }
    (* case l contains at least one 1 *)
    move=> [k1] [l' ->]. have [|]:= list_symbol_shape l'.
      (* case l' contains only 0s *)
    { 
      move=> [k2 ->]. pose k := (S m) / (1+n).
      have [? | ?] : k <= k2 \/ k2 < k by lia.
        (* case k2 is large enough *)
      {
        have [/in_iPI [j'] [n'] Hjj'n' | Hj]: j < length P \/ length P <= j by lia.
          (* case j is a valid instruction index *)
        { 
          have := maybe_increase_next [] r i j n (S m) k2 k1 Hijn ltac:(lia).
          move Hm': (k1 + S m + S m / (1 + n) + S m mod (1 + n)) => m'.
          move: (k2 - S m / (1 + n)) => m'' H.
          have ? := @div_mod_pos n m.
          exists (([§1] ++ r), (§0^(m' - (S m + 1)) ++ [§1] ++ §0^m''), n', (#+j), (#-j)).
          move: H.
          apply: (maybe_reachable_trans' 1); [by lia | by rewrite ?app_norm |].
          apply: (maybe_first_step (index_try_spec (j, (j', n'))) r (§0^(m'-1) ++ [§1] ++ §0^m''));
            [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
          apply: maybe_reachable_refl'. rewrite ?app_norm. do 4 f_equal. by lia.
        }
        (* case j is not a valid instruction index *)
        exists dummy.
        have := maybe_increase_next [] r i j n (S m) k2 k1 Hijn ltac:(lia).
        apply: (maybe_reachable_trans' 0); [by lia | by rewrite ?app_norm |].
        apply: terminal_maybe_reachable. by apply: large_index_terminal.
      }
      (* case k2 is too small *)
      exists dummy.
      have := maybe_increase_stop r i j n (S m) k2 k1 
        ([§0], §0^(S m + 1) ++ [§0], goto 0 +| +|) Hijn ltac:(lia).
      by apply: maybe_reachable_mon'; first by lia.
    }
    (* case l' contains at least one 1 *)
    move=> [k2] [{}l' ->]. pose k := (S m) / (1+n).
    have [? | ?]: k <= k2 \/ k2 < k by lia.
      (* case k2 is large enough *)
    { 
      have [/in_iPI [j'] [n'] Hjj'n' | Hj] : j < length P \/ length P <= j by lia.
        (* case j is a valid instruction index *)
      {  
        have := maybe_increase_next ([§1] ++ l') r i j n (S m) k2 k1 Hijn ltac:(lia).
        move Hm': (k1 + S m + S m / (1 + n) + S m mod (1 + n)) => m'.
        move: (k2 - S m / (1 + n)) => m'' H.
        have ? := @div_mod_pos n m.
        exists (([§1] ++ r), (§0^(m' - (S m + 1)) ++ [§1] ++ §0^m'' ++ [§1] ++ l'), n', (#+j), (#-j)).
        move: H.
        apply: (maybe_reachable_trans' 1); [by lia | by rewrite ?app_norm |].
        apply: (maybe_first_step (index_try_spec (j, (j', n'))) r (§0^(m'-1) ++ [§1] ++ §0^m'' ++ [§1] ++ l'));
          [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
        apply: maybe_reachable_refl'. rewrite ?app_norm. do 4 f_equal. by lia.
      }
      (* case j is not a valid instruction index *)
      exists dummy.
      have := maybe_increase_next ([§1] ++ l') r i j n (S m) k2 k1 Hijn ltac:(lia).
      apply: (maybe_reachable_trans' 0); [by lia | by rewrite ?app_norm |].
      apply: terminal_maybe_reachable. by apply: large_index_terminal.
    }
    (* case k2 is too small *)
    have [[[[[l'' r''] n''] X''] Y''] Hz] := 
      maybe_bounded_yes_grow ([§1] ++ r) ([§1] ++ l') (S m + k1 + k2 + 1).
    exists (l'', (§0^(k1 + k2 + 1) ++ r''), n'', X'', Y''). 
    have := maybe_increase_fail l' r i j n (S m) k2 k1 Hijn ltac:(lia).
    apply: (maybe_reachable_trans' 1); [by lia | done |].
    move: Hz. apply: maybe_reachable_mon'; first by lia.
    rewrite ?app_norm. do 5 f_equal. by lia.
  Qed.

  Definition maybe_index_try_grow_time := maybe_index_try_futile_time + (length P) * maybe_index_try_step_time + maybe_index_yes_grow_time + maybe_goto_1_time + 1.

  Lemma maybe_index_try_grow l r m i : exists '(l', r', n, X, Y), 
    maybe_reachable maybe_index_try_grow_time (l, §0^m ++ r, '#?i) (l', §0^(m+1) ++ r', goto n X Y).
  Proof using NP_spec.
    rewrite /maybe_index_try_grow_time. pose dummy := ([§0], [§0], 0, +|, +|).
    have [[n ->]|] := list_symbol_shape r.
    { exists dummy. apply: (maybe_reachable_mon' (n := maybe_index_try_futile_time)); 
        [by lia | by rewrite ?app_norm; reflexivity | by apply: maybe_index_try_futile]. }
    move=> [n [+ ->]] => {}r. move Hk: (length P - i) => k.
    suff: exists '(l', r', n', X', Y'), maybe_reachable 
      (maybe_index_try_futile_time + k * maybe_index_try_step_time + maybe_index_yes_grow_time + maybe_goto_1_time + 1)
      (l, §0^(m+n) ++ [§1] ++ r, '#? i) (l', §0^((m+n)+1) ++ r', goto n' X' Y').
    { move=> [[[[[l' r'] n'] X'] Y'] H]. exists (l', §0^n ++ r', n', X', Y').
      move: H. apply: maybe_reachable_mon'; first by (rewrite /maybe_index_try_grow_time; lia).
      rewrite ?app_norm. do 5 f_equal. by lia. }
    move: (m + n) l => {}m {n} [|a l]. 
      (* case l is empty *)
    { exists dummy. by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?]. }
    case: a.
      (* case l starts with 0 *)
    { exists dummy. by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?]. }
    move: r m => r [|m].
      (* case m is empty *)
    { exists dummy. by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?]. }
    elim: k i r Hk.
      (* case i is not a valid instruction index *) 
    { move=> *. exists dummy. apply: terminal_maybe_reachable. apply: large_index_terminal. by lia. }
    (* case i is a valid instruction *)
    move=> k IH i r Hk /=. have /in_iPI [j [n Hijn]] : i < length P by lia.
    pose x := {| CM.state := i; CM.value := S m |}.
    move Hi'm': (CM.step P x) => [i' m'].
    have := CM_facts.step_progress P x.
    move /(_ ltac:(rewrite /x /=; lia) ltac:(rewrite /x /=; lia)). case.
      (* counter value did not increase *)
    {
      rewrite Hi'm'. move=> [? ?]. subst i' m'.
      have [e He] := IH (1+i) r ltac:(lia).
      exists e. move: e He => [[[[? ?] ?] ?] ?] He.
      have := maybe_index_try_step l r x.
      rewrite /x Hi'm' /= ?nat_norm ?app_norm.
      by apply: (maybe_reachable_trans' 
        (maybe_index_try_futile_time + k * maybe_index_try_step_time + maybe_index_yes_grow_time + maybe_goto_1_time + 1)); first by lia.
    }
    (* case counter value did increase *)
    move=> Hx. have [[j' n'] [/nth_error_Some_In_iP HxIp /= Hmn']] := CM_facts.inc_value_mod Hx.

    have [e He] := maybe_index_yes_grow ([§1] ++ r) ([§1] ++ l) (S m) i.
    exists e. move: e He => [[[[? ?] ?] ?] ?] He.
    apply: (maybe_first_step (index_try_spec (i, (j, n))) l (§0^m ++ [§1] ++ r)); 
      [ by nia  | by auto with M | by rewrite ?app_norm | ]. 

    rewrite ?app_norm. apply: (maybe_first_goto_1 maybe_index_yes_grow_time); first by nia.
    subst x. have [_ ->]:= in_iP_unique (n := n) (n' := n') ltac:(eassumption) ltac:(eassumption).
    rewrite Hmn'. move: He. by apply: maybe_reachable_mon'; first by lia.
  Qed.
  
  Lemma maybe_increase_try_grow l r m i :
    exists '(l', r', n, X, Y), maybe_reachable 1 (l, §0^m ++ r, '$?i) (l', §0^(m+1) ++ r', goto n X Y).
  Proof.
    pose dummy := ([§0], [§0], 0, +|, +|).
    have [? | /in_iPI [j] [n] ?]: length P <= i \/ i < length P by lia.
    { exists dummy. apply: terminal_maybe_reachable. by apply: large_increase_terminal. }
    move: l => [|a [|b l]].
    (* case l is empty *)
    - exists dummy. by apply: terminal_maybe_reachable => ? /increase_try_step_shape [|].
    (* case l is singleton *)
    - exists dummy. by apply: terminal_maybe_reachable => ? /increase_try_step_shape [|].
    (* case l has at least two symbols *)
    - case: a.
      { exists dummy. by apply: terminal_maybe_reachable => ? /increase_try_step_shape [|]. }
      case: b.
      (* use increase_try_spec_0 *)
      * exists (([§1] ++ l), r, 0, ($+i), ($+i)).
        apply: (maybe_first_step (increase_try_spec_0 (i, (j, n))) l (§0^m ++ r));
          [by lia | by auto with M | done |].
        rewrite ?app_norm. apply: maybe_reachable_refl'. do 4 f_equal. by lia.
      (* use increase_try_spec_1 *)
      * exists (([§1] ++ l), r, 0, ($-i), ($-i)).
        apply: (maybe_first_step (increase_try_spec_1 (i, (j, n))) l (§0^m ++ r));
          [by lia | by auto with M | done |].
        rewrite ?app_norm. apply: maybe_reachable_refl'. do 4 f_equal. by lia.
  Qed.  

  Definition maybe_increase_yes_grow_time := maybe_index_try_grow_time + maybe_index_yes_futile_time + 2.

  Lemma maybe_increase_yes_grow l r m i : exists '(l', r', n, X, Y), 
    maybe_reachable maybe_increase_yes_grow_time (l, §0^m ++ r, '$+i) (l', §0^(m+1) ++ r', goto n X Y).
  Proof using NP_spec.
    pose dummy := ([§0], [§0], 0, +|, +|). rewrite /maybe_increase_yes_grow_time.
    have [? | /in_iPI [j [n Hijn]]]: length P <= i \/ i < length P by lia.
      (* case i is not a valid instruction index *)
    { exists dummy. apply: terminal_maybe_reachable. by apply: large_increase_terminal. }
    (* case i is a valid instruction index *)
    move: l => [|a l].
      (* case l is empty *)
    { exists dummy. by apply: terminal_maybe_reachable => ? /increase_yes_step_shape. }
    case: a.
      (* case l starts with 0 *)
    { exists dummy. by apply: terminal_maybe_reachable => ? /increase_yes_step_shape. }
    (* case l starts with 1 *)
    have [|]:= list_symbol_shape l.
      (* case l is 1; 0; 0; 0; ... *)
    {
      move=> [m' ->]. exists dummy.
      apply: (maybe_first_step (increase_yes_spec (i, (j, n))) (§0^m') (§0^m ++ r));
        [ by lia | by auto with M | by rewrite ?app_norm | ].

      apply: (maybe_reachable_mon' (n := maybe_index_yes_futile_time)); 
        [by lia | by rewrite ?app_norm; reflexivity | by apply: maybe_index_yes_futile].
    }
    (* case: l contains a second 1 *)
    move=> [m' [+ ->]] => {}l.
    have [-> |] : m' = 0 \/ (0 < m' /\ m' < n+1) \/ n+1 <= m' by lia.
      (* case l starts with is 1; 1 *)
    {
      have [e He] := maybe_index_try_grow ([§1] ++ l) (§0^1 ++ r) m j.
      exists e. move: e He => [[[[l' r'] n'] X'] Y'] He.
      apply: (maybe_first_step (increase_yes_spec (i, (j, n))) ([§1] ++ l) (§0^m ++ r));
        [by lia | by auto with M | by rewrite ?app_norm | ].
      
      apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) (§0^(1 + m) ++ r) l);
        [by lia | by auto with M | by rewrite ?app_norm | ].

      move: He. apply: maybe_reachable_mon'; first by lia.
      rewrite ?app_norm. do 5 f_equal. by lia.
    }
    case=> Hm'.
      (* case l starts with is 1; 0s; 1 with too few 0s *)
    {
      exists dummy.
      apply: (maybe_first_step (increase_yes_spec (i, (j, n))) (§0^m' ++ [§1] ++ l) (§0^m ++ r));
        [ by lia | by auto with M | by rewrite ?app_norm |].

      apply: terminal_maybe_reachable. rewrite ?app_norm. have ->: m' = 1+(m'-1) by lia.
      move=> ? /(index_yes_step_shape Hijn) [| /zero_prefix_lt]; by [| lia].
    }
    (* case l starts with is 1; 0s with enough 0s *)
    exists (([§1] ++ §0^(m' - (n + 1)) ++ [§1] ++ l), (§0^n ++ r), 0, $?i, $?i).
    apply: (maybe_first_step (increase_yes_spec (i, (j, n))) (§0^m' ++ [§1] ++ l) (§0^m ++ r));
      [ by lia | by auto with M | by rewrite ?app_norm |].

    apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^(1+m) ++ r) (§0^(m'-(n+1)) ++ [§1] ++ l));
      [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
    
    apply: maybe_reachable_refl'. rewrite ?app_norm. do 4 f_equal. by lia.
  Qed.

  Definition maybe_index_no_grow_time := maybe_index_try_grow_time + maybe_goto_1_time + maybe_index_try_stop_time + 3.

  Lemma maybe_index_no_grow l r m i : exists '(l', r', n, X, Y), 
    maybe_reachable maybe_index_no_grow_time (l, §0^m ++ r, '#-i) (l', §0^(m+1) ++ r', goto n X Y).
  Proof using NP_spec.
    pose dummy := ([§0], [§0], 0, +|, +|). rewrite /maybe_index_no_grow_time.
    have [? | /in_iPI [j [n Hjn]]] : length P <= i \/ i < length P by lia.
      (* case i is not a valid instruction index *)
    { exists dummy. apply: terminal_maybe_reachable. by apply: large_index_terminal. }
    (* case i is a valid instruction index *)
    case: (list_symbol_shape r).
      (* case r contains only 0s *)
    {
      move=> [m' ->]. exists dummy. rewrite ?app_norm. case: (m + m').
        (* case r is empty *)
      { by apply: terminal_maybe_reachable => ? /index_no_step_shape. }
      (* case r starts with 0 *)
      move=> {}m'.
      apply: (maybe_first_step (index_no_spec (i, (j, n))) l (§0^m'));
        [by lia | by auto with M | by rewrite ?app_norm |].
      rewrite ?app_norm. apply: maybe_goto_1_futile. by lia.
    }
    (* case r contains an 1 *)
    move=> [m' [+ ->]] => {}r. rewrite ?app_norm.
    move Hm'': (m + m') => m''. move: m'' Hm'' => [|m''] Hm''.
      (* case r starts with 1 *)
    { exists dummy. by apply: terminal_maybe_reachable => ? /index_no_step_shape. }
    (* case r starts with 0 *)
    have [e He] := maybe_index_try_grow ([§1] ++ r) (§0^m' ++ l) m (1+i).
    exists e. move: e He => [[[[l' r'] n'] X'] Y'] He.
    apply: (maybe_first_step (index_no_spec (i, (j, n))) l (§0^m'' ++ [§1] ++ r));
      [by lia | by auto with M | by rewrite ?app_norm | ].
    rewrite ?app_norm. apply: (maybe_first_goto_1 maybe_index_try_grow_time); first by lia.
    move: He. apply: maybe_reachable_mon'; [by lia | by rewrite ?app_norm Hm''].
  Qed.

  Definition maybe_bounded_try_grow_time := maybe_bounded_try_time+1.

  Lemma maybe_bounded_try_grow l r m : exists '(l', r', n, X, Y), 
    maybe_reachable maybe_bounded_try_grow_time (l, §0^m ++ r, '?|) (l', §0^(m+1) ++ r', goto n X Y).
  Proof using NP_spec.
    rewrite /maybe_bounded_try_grow_time.
    move: m => [|m]; first last.
    { exists ([], [], 0, +|, +|). by apply: terminal_maybe_reachable => ? /bound_try_step_shape [? ?]. }
    have [e He] := maybe_bounded_yes_grow r l 0.
    exists e. move: e He => [[[[l' r'] n] X] Y] He.
    have := maybe_bounded_try r l.
    by apply: (maybe_reachable_trans' 1); first by lia.
  Qed.

  Definition maybe_basic_state_grow_time :=     
    maybe_index_try_stop_time + 2 +
    maybe_bounded_try_grow_time +
    maybe_index_try_grow_time + maybe_index_yes_grow_time + maybe_index_no_grow_time +
    maybe_increase_yes_grow_time + maybe_increase_no_grow_time.

  Lemma maybe_basic_state_grow l r m X : exists '(l', r', n', X', Y'), 
    maybe_reachable maybe_basic_state_grow_time (l, §0^m ++ r, basic_state X) (l', §0^(m+1) ++ r', goto n' X' Y').
  Proof using NP_spec.
    rewrite /maybe_basic_state_grow_time.
    case: X.
    - case. 
      + have [e He] := maybe_bounded_yes_grow l r m.
        exists e. move: e He => [[[[l' r'] n'] X'] Y'].
        by apply: maybe_reachable_mon'; [ lia | ].
      + have [e He] := maybe_bounded_try_grow l r m.
        exists e. move: e He => [[[[l' r'] n'] X'] Y'].
        by apply: maybe_reachable_mon'; [ lia | ].
    - case=> i.
      + have [e He] := maybe_index_try_grow l r m i.
        exists e. move: e He => [[[[l' r'] n'] X'] Y'].
        by apply: maybe_reachable_mon'; [ lia | ].
      + have [e He] := maybe_index_yes_grow l r m i.
        exists e. move: e He => [[[[l' r'] n'] X'] Y'].
        by apply: maybe_reachable_mon'; [ lia | ].
      + have [e He] := maybe_index_no_grow l r m i.
        exists e. move: e He => [[[[l' r'] n'] X'] Y'].
        by apply: maybe_reachable_mon'; [ lia | ].
    - case=> i.
      + have [e He] := maybe_increase_try_grow l r m i.
        exists e. move: e He => [[[[l' r'] n'] X'] Y'].
        by apply: maybe_reachable_mon'; [ lia | ].
      + have [e He] := maybe_increase_yes_grow l r m i.
        exists e. move: e He => [[[[l' r'] n'] X'] Y'].
        by apply: maybe_reachable_mon'; [ lia | ].
      + have [e He] := maybe_increase_no_grow l r m i.
        exists e. move: e He => [[[[l' r'] n'] X'] Y'].
        by apply: maybe_reachable_mon'; [ lia | ].
  Qed.

  Definition maybe_goto_1_grow_time :=
    maybe_basic_state_grow_time + maybe_goto_1_time.

  Lemma maybe_goto_1_grow l r m n X Y : exists '(l', r', n', X', Y'), 
    maybe_reachable maybe_goto_1_grow_time (l, §0^m ++ r, goto n X Y) (l', §0^(m+1) ++ r', goto n' X' Y').
  Proof using NP_spec.
    rewrite /maybe_goto_1_grow_time.
    case: (list_symbol_shape r).
      (* case r has only 0s *)
    { move=> [m' ->]. exists ([], [], 0, +|, +|).
      rewrite /maybe_basic_state_grow_time ?app_norm. apply: maybe_goto_1_futile. by lia. }
    (* case r hast at least one 1 *)
    move=> [m' [+ ->]] => {}r. rewrite ?app_norm.
    move Hk: ((m + m') mod (n + 1)) => k. move: k Hk => [|k] Hk.
      (* case goto produces X *)
    {
      have [e He] := maybe_basic_state_grow ([§1] ++ r) (§0^m' ++ l) m X.
      exists e. move: e He => [[[[l' r'] n'] X'] Y'] He.
      apply: (maybe_first_goto_1 maybe_basic_state_grow_time); first by lia.
      rewrite Hk. move: He. apply: maybe_reachable_mon'; [by lia | by rewrite ?app_norm].
    }
    (* case goto produces Y *)
    have [e He] := maybe_basic_state_grow ([§1] ++ r) (§0^m' ++ l) m Y.
    exists e. move: e He => [[[[l' r'] n'] X'] Y'] He.
    apply: (maybe_first_goto_1 maybe_basic_state_grow_time); first by lia.
    rewrite Hk. move: He. apply: maybe_reachable_mon'; [by lia | by rewrite ?app_norm].
  Qed.

  Lemma maybe_goto_1_grow_iter l r m n X Y : exists '(l', r', n', X', Y'), 
    maybe_reachable (m*maybe_goto_1_grow_time) (l, r, goto n X Y) (l', §0^m ++ r', goto n' X' Y').
  Proof using NP_spec.
    elim: m l r n X Y.
    { move=> l r n X Y. exists (l, r, n, X, Y). by apply: maybe_reachable_refl'. }
    move=> m + l r n X Y.
    move /(_ l r n X Y) => [[[[[l' r'] n'] X'] Y'] He'].
    have [e He] := maybe_goto_1_grow l' r' m n' X' Y'.
    exists e. move: e He => [[[[l'' r''] n''] X''] Y''] He.
    move: He'. apply: (maybe_reachable_trans' maybe_goto_1_grow_time); 
      [by lia |done | by have ->: (S m) = m+1 by lia].
  Qed.

  (* uniform upper bound on stack machine termination (from any configuration) *)
  Definition uniform_termination_time := 
    ((G + (CP + 1)) * maybe_goto_1_grow_time) + (NP * step_time CP TP + 2) + maybe_basic_state_grow_time.

  Theorem uniform_termination x: exists z, 
    reachable_n uniform_termination_time x z /\ terminal M z.
  Proof using NP_spec.
    apply: universal_maybe_reachable_terminal => z. rewrite /uniform_termination_time.
    move: x => [[l r] [X|n X Y]].
    {
      have [[[[[l' r'] n'] X'] Y']] := maybe_basic_state_grow l r 0 X.
      apply: (maybe_reachable_trans' ((G + (CP + 1)) * maybe_goto_1_grow_time + (NP * step_time CP TP + 2)));
        [ by lia | done | ].
      have [[[[[l'' r''] n''] X''] Y'']] := maybe_goto_1_grow_iter l' (§0^1 ++ r') (G + (CP + 1)) n' X' Y'.
      apply: (maybe_reachable_trans' (NP * step_time CP TP + 2));
        [ by lia | done | ].
      apply: maybe_goto_1_far; by lia.
    }
    have [[[[[l'' r''] n''] X''] Y'']] := maybe_goto_1_grow_iter l r (G + (CP + 1)) n X Y.
    apply: (maybe_reachable_trans' (NP * step_time CP TP + 2));
      [ by lia | done | ].
    apply: maybe_goto_1_far; by lia.
  Qed.

  Local Definition clos_rt_rt1n_iff := @clos_rt_rt1n_iff (@SM.Config State Symbol).

  (* compute the list of all reachable configurations *)
  Lemma reachable_configurations {T x z} : reachable_n T x z -> terminal M z -> 
    exists L, (forall y, SM.reachable M x y -> In y L) /\ length L <= S T.
  Proof.
    elim: T x z.
    {
      move=> x z. move HT: (0) => T Hxz. case: Hxz HT; last done.
      move=> ? {}x <- Hx. exists [x]. constructor; last by (move=> /=; lia).
      move=> y /clos_rt_rt1n_iff Hxy. case: Hxy Hx; first by (move=> *; left).
      by move=> > + ? Hx => /Hx.
    }
    move=> T IH x z. move HT': (S T) => T' Hxz.
    case: Hxz HT'.
    {
      move=> ? {}x <- Hx. exists [x]. constructor; last by (move=> /=; lia).
      move=> y /clos_rt_rt1n_iff Hxy. case: Hxy Hx; first by (move=> *; left).
      by move=> > + ? Hx => /Hx.
    }
    move=> {}T' {}x y {}z Hxy Hyz ?.
    have ?: T = T' by lia. subst T'.
    move /(IH y _ Hyz) => [L [H1L H2L]]. exists (x :: L). constructor; first last.
    { rewrite /length -/(length _). by lia. }
    move=> y'. move HT': (1 + T) => T' /clos_rt_rt1n_iff Hxy'. 
    case: Hxy' HT' Hxy; first by (move=> *; left).
    move=> {}y' z' Hxy' Hy'z' ? Hxy. right.
    apply: H1L. have -> : y = y' by apply: deterministic_M; eassumption.
    by apply /clos_rt_rt1n_iff.
  Qed.

  (* if counter machine halts, then stack machine is uniformly bounded *)
  Theorem terminating_P_to_bounded_M : SM.bounded M (1+uniform_termination_time).
  Proof using NP_spec.
    rewrite /SM.bounded. move=> x.
    have [z [Hz]]:= uniform_termination x.
    by move /(reachable_configurations Hz).
  Qed.

  End Transport.

End Reduction.
