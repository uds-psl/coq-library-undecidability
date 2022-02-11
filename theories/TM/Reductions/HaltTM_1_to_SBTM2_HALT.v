From Undecidability Require TM.TM TM.Util.TM_facts.
From Undecidability Require Import TM.SBTM2.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.

Require Import PeanoNat Lia.

#[local] Unset Implicit Arguments.
#[local] Unset Strict Implicit.

Require Import List ssreflect ssrbool ssrfun.
Import ListNotations.

Module SBTM2_facts.

  (* remove redundante false symbol *)
  Definition truncate (l : list bool) : list bool :=
    match l with
    | [false] => []
    | [a; false] => if a then [a] else []
    | _ => l
    end.

  Definition truncate_tape (t : tape) : tape :=
    match t with
    | (ls, a, rs) => (truncate ls, a, truncate rs)
    end.

  Lemma iter_plus {X} (f : X -> X) (x : X) n m : Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
  Proof.
    elim: m; first by rewrite Nat.add_0_r.
    move=> m /= <-. by have ->: n + S m = S n + m by lia.
  Qed.

  (* two lists differ only in trailing false symbols *)
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
    - move=> ???? /=. case: (trans M _); last done.
      move=> [[? ?] []] [] <- <- [] <- <- /=; by do ? constructor.
    - move=> n'1 n'2 /=. case: (trans M _); last done.
      move=> [[? ?] []] [] <- <- [] <- <- /=; first by do ? constructor.
      move: n'1 n'2 => [|?] [|?] /=; by do ? constructor.
    - move=> ???? /=. case: (trans M _); last done.
      move=> [[? ?] []] [] <- <- [] <- <- /=; last by do ? constructor.
      move: n1 n2 => [|?] [|?] /=; by do ? constructor.
    - move=> n'1 n'2 /=. case: (trans M _); last done.
      move=> [[? ?] []] [] <- <- [] <- <- /=.
      + move: n1 n2 => [|?] [|?] /=; by do ? constructor.
      + move: n'1 n'2 => [|?] [|?] /=; by do ? constructor.
  Qed.

  Lemma almost_eq_tape_step_None M q t1 t2 :
    almost_eq_tape t1 t2 -> 
    step M (q, t1) = None ->
    step M (q, t2) = None.
  Proof.
    case=> a ???? [] => [????|n1 n2] [] > /=.
    all: case: (trans M _); last done.
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

  Lemma almost_eq_truncate l : almost_eq l (truncate l).
  Proof.
    have ? := almost_eq_refl.
    have ? := almost_eq_false 0 0.
    have ? := almost_eq_false 1 0.
    have ? := almost_eq_false 2 0.
    move: l => [|[] [|[] [|??]]] /=; by do ? constructor.
  Qed.

  Lemma almost_eq_tape_truncate_tape t : almost_eq_tape t (truncate_tape t).
  Proof.
    move: t => [[ls a] rs]. constructor; by apply: almost_eq_truncate.
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

  #[local] Opaque step.

  Lemma steps_truncate {M k q t} :
    steps M k (q, truncate_tape t) = None <-> (steps M k (q, t) = None).
  Proof.
    have := almost_eq_tape_truncate_tape t.
    move: (truncate_tape t) => t'.
    elim: k q t t'; first done.
    move=> k IH q t t'. rewrite !(steps_plus 1 k) /=.
    case E1: (step M (q, t)) => [[q2 t2]|];
      case E2: (step M (q, t')) => [[q'2 t'2]|].
    - move: E1 E2 => /almost_eq_tape_step_Some /[apply] /[apply].
      move=> [<- /IH]. by apply.
    - move=> /almost_eq_tape_sym Ht't.
      by move: E2 Ht't E1 => /almost_eq_tape_step_None /[apply] ->.
    - move=> Htt'.
      by  move: E1 Htt' E2 => /almost_eq_tape_step_None /[apply] ->.
    - done.
  Qed.

End SBTM2_facts.

(* translate between Fin and a listable type *)
Module ListFin.
  Fixpoint decode {X : Type} (L : list X) (i : Fin.t (length L)) : X :=
    (match L return Fin.t (length L) -> X with
    | [] => fun j => Fin.case0 (fun=> X) j
    | x :: L' => fun j => Fin.caseS' j (fun=> X) x (fun j' => decode L' j')
    end) i.

  Definition encode_sig
    {X : Type} (HX : forall (x y : X), {x = y} + {x <> y})
    {L : list X} (HL : forall x, In x L) (x : X) :
      {i : Fin.t (length L) | decode L i = x }.
  Proof.
    elim: L {HL} (HL x); first done.
    move=> y L IH /=. case: (HX y x).
    - move=> -> _. by exists Fin.F1.
    - move=> ??. have /IH [i Hi] : In x L by tauto.
      by exists (Fin.FS i).
  Qed.

  Definition encode
    {X : Type} (HX : forall (x y : X), {x = y} + {x <> y})
    {L : list X} (HL : forall x, In x L) (x : X) :
      Fin.t (length L) := sval (encode_sig HX HL x).

  Lemma decode_encode 
    {X : Type} (HX : forall (x y : X), {x = y} + {x <> y})
    {L : list X} (HL : forall x, In x L)
    (x : X) : decode L (encode HX HL x) = x.
  Proof. exact: (svalP (encode_sig HX HL x)). Qed.
End ListFin.

Import SBTM2_facts.

Section Construction.
  (* input TM *)
  Context (M : TM.TM (finType_CS bool) 1).

  (* symbols are "01", "11" *)
  Definition encode_symbol (a : finType_CS bool) : list bool := [a; true].

  (* blank is 00 *)
  Definition encode_tape (t : TM.tape (finType_CS bool)) : tape :=
    match t with
    | TM.niltape => ([], false, [])
    | TM.leftof a rs => ([], false, flat_map encode_symbol (a :: rs))
    | TM.rightof a ls => (false :: flat_map (fun a' => rev (encode_symbol a')) (a :: ls), false, [])
    | TM.midtape ls a rs => (a :: flat_map (fun a' => rev (encode_symbol a')) ls, true, flat_map encode_symbol rs)
    end.

  Inductive space : Type :=
  (* corresponds to q *)
  | space_base (q : TM.state M) : space
  (* reading symbol *)
  | space_read (q : TM.state M) : space
  (* stepping twice in direction d *)
  | space_move (q : TM.state M) (d : direction) (t : bool) : space 
  (* test next symbol in direction d: on false return, on true q *)
  | space_test (q : TM.state M) (d : direction) (t : bool) : space
  (* write b then move in direction *)
  | space_write (q : TM.state M) (a : bool) (d : TM.move) : space.
  
  Lemma listable_space : {L : list space | forall x, In x L}.
  Proof.
    have : {L' | forall (d : direction) (t : bool) (m : TM.move), In (d, t, m) L'}.
    { exists (list_prod (list_prod [go_left; go_right] [true; false]) [TM.Lmove; TM.Rmove; TM.Nmove]).
      move=> [] [] [] /=; tauto. }
    move=> [L' HL'].
    exists (
      flat_map (fun '(q, (d, t, m)) =>
        [space_base q; space_read q; space_move q d t; space_test q d t; space_write q t m]) 
        (list_prod (elem (TM.state M)) L')).
    move=> [].
    - move=> q. apply /in_flat_map.
      exists (q, (go_left, true, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q. apply /in_flat_map.
      exists (q, (go_left, true, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q d t. apply /in_flat_map.
      exists (q, (d, t, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q d t. apply /in_flat_map.
      exists (q, (d, t, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q a m. apply /in_flat_map.
      exists (q, (go_left, a, m)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
  Qed.

  Lemma eqdec_space : forall (x y : space), {x = y} + {x <> y}.
  Proof.
    have := @eqType_dec (TM.state M). move=> H.
    intros. do ? decide equality; by apply: H.
  Qed.

  #[local] Notation size := (length (sval listable_space)).

  Definition encode_space : space -> Fin.t size :=
    fun x => ListFin.encode eqdec_space (svalP listable_space) x.

  Definition decode_space : Fin.t size -> space :=
    fun x => ListFin.decode (sval listable_space) x.

  Lemma decode_encode_space (x : space) : decode_space (encode_space x) = x.
  Proof. by apply: ListFin.decode_encode. Qed.

  #[local] Notation "| a |" := (Vector.cons _ a 0 (Vector.nil _)).

  #[local] Notation encode_state q := (encode_space (space_base q)).

  Definition go_back (d : direction) :=
    match d with
    | go_left => go_right
    | go_right => go_left
    end.

  Definition M' : SBTM2.
  Proof.
    refine (Build_SBTM2 size
      (fun '(q, a) => _)).
    (* in state q reading symbol a *)
    refine (
      match decode_space q with
      | space_base q_base => _
      | space_read q_read => _
      (* move d twice *)
      | space_move q' d true => 
          Some (encode_space (space_move q' d false), a, d)
      (* move d once *)
      | space_move q' d false => 
          Some (encode_state q', a, d)
      (* test d in distance 1 *)
      | space_test q' d true => 
          Some (encode_space (space_test q' d false), a, d)
      (* test *)
      | space_test q' d false => 
          match a with
          | true => Some (encode_space (space_move q' go_right false), a, go_left)
          | false => Some (encode_space (space_move q' (go_back d) false), a, go_back d)
          end
      (* write *)
      | space_write q' b TM.Lmove =>
          Some (encode_state q', b, go_left)
      | space_write q' b TM.Rmove =>
          Some (encode_space (space_move q' go_right true), b, go_right)
      | space_write q' b TM.Nmove =>
          Some (encode_state q', b, go_right)
      end).
    + (* case space_base *)
      refine (
        match TM.halt M q_base with
        (* halting condition *)
        | true => None
        | false =>
            match a with
            (* a = true, read actual symbol *)
            | true => Some (encode_space (space_read q_base), true, go_left)
            (* case a = false, no symbol *)
            | false => 
              match TM.trans M (q_base, | None |) with
              | (q_next, result) =>
                  match Vector.hd result with
                  (* case write b, move *)
                  | (Some b, m) => Some (encode_space (space_write q_next b m), true, go_left)
                  (* case no write *)
                  | (None, TM.Lmove) => Some (encode_space (space_test q_next go_left true), a, go_left)
                  | (None, TM.Rmove) => Some (encode_space (space_test q_next go_right true), a, go_right)
                  | (None, TM.Nmove) =>  Some (encode_space (space_move q_next go_right false), a, go_left)
                  end
              end
            end
        end).
    + (* case space_read *)
      refine ( 
        match TM.trans M (q_read, | Some a |) with
        | (q_next, result) =>
          match Vector.hd result with
          (* case write bL, Lmove *)
          | (Some bL, TM.Lmove) => Some (encode_state q_next, bL, go_left)
          (* case write bR, Rmove *)
          | (Some bR, TM.Rmove) => Some (encode_space (space_move q_next go_right true), bR, go_right)
          (* case write bN, Nmove *)
          | (Some bN, TM.Nmove) => Some (encode_state q_next, bN, go_right)
          (* case no write *)
          | (None, TM.Lmove) => Some (encode_state q_next, a, go_left)
          | (None, TM.Rmove) => Some (encode_space (space_move q_next go_right true), a, go_right)
          | (None, TM.Nmove) => Some (encode_state q_next, a, go_right)
          end
        end).
  Defined.

  #[local] Notation step := (step M').
  #[local] Notation steps := (steps M').
  #[local] Notation state := (state M').
  #[local] Notation config := (config M').

  #[local] Notation TM_step x := (@TM_facts.step _ _ M x).
  #[local] Notation TM_config := (@TM_facts.mconfig (finType_CS bool) (TM.state M) 1).

  Definition encode_config : TM_config -> config :=
    fun '(TM_facts.mk_mconfig q ctapes) =>
      (encode_state q, truncate_tape (encode_tape (Vector.hd ctapes))).

  (* simulation up to truncation *)
  Lemma simulation_step q t : TM.halt M q = false ->
    exists k,
      (omap (fun '(q', t') => (q', truncate_tape t')) (steps (S k) (encode_state q, encode_tape t))) =
        Some (encode_config (TM_step (TM_facts.mk_mconfig q (| t |)))).
  Proof.
    move=> Hq. case: t.
    - (* case niltape *)
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= decode_encode_space ?E ?Hq.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. by do ? rewrite /= decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= decode_encode_space ?E ?Hq.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
    - (* case leftof *)
      move=> a rs.
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= decode_encode_space ?E ?Hq.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. by do ? rewrite /= decode_encode_space ?E ?Hq.
        * exists 3. do ? rewrite /= decode_encode_space ?E ?Hq.
          by case: a.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
    - (* case rightof *)
      move=> a ls.
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= decode_encode_space ?E ?Hq.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. by do ? rewrite /= decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= decode_encode_space ?E ?Hq.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
    - (* case midtape *)
      move=> ls a rs.
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. do ? rewrite /= decode_encode_space ?E ?Hq.
          move: ls => [|l ls]; by do ? rewrite /= decode_encode_space.
        * exists 1. do ? rewrite /= decode_encode_space ?E ?Hq.
          move: ls => [|l ls]; by do ? rewrite /= decode_encode_space.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. do ? rewrite /= decode_encode_space ?E ?Hq.
          move: rs => [|r rs]; by do ? rewrite /= decode_encode_space.
        * exists 3. do ? rewrite /= decode_encode_space ?E ?Hq.
          move: rs => [|r rs]; by do ? rewrite /= decode_encode_space.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= decode_encode_space ?E ?Hq.
  Qed.

  Lemma simulation_halt q t : TM.halt M q = true ->
    step (encode_state q, t) = None.
  Proof.
    move: t => [[? ?] ?] /= Hq.
    by rewrite /= decode_encode_space ?Hq.
  Qed.

  Lemma simulation q t :
    (exists q' t', TM.eval M q t q' t') ->
    exists k, steps k ((encode_state q), (encode_tape (Vector.hd t))) = None.
  Proof.
    move=> [q'] [t'] /TM_facts.TM_eval_iff [n].
    elim: n q t.
    { move=> q t. rewrite /= /TM_facts.haltConf /=.
      case E: (TM.halt q) => [|]; last done.
      move: E => /simulation_halt H _.
      exists 1. by apply: H. }
    move=> n IH q t. rewrite /= /TM_facts.haltConf /=.
    case E: (TM.halt q) => [|].
    { move: E => /simulation_halt H _. exists 1. by apply: H. }
    rewrite (Vector.eta t).
    move: E => /simulation_step => /(_ (Vector.hd t)) [k1].
    move: (VectorDef.tl t). apply: Vector.case0.
    move: (TM_step _) => [q'' ts''] Hk1 /IH [k2 Hk2] /=.
    exists ((S k1) + k2). rewrite (steps_plus).
    move: (encode_state q, _) Hk1 Hk2 => x.
    move Hk1: (steps (S k1) x) => [[q''' t''']|] /=; last done.
    move=> [] <- Ht''' /(@steps_truncate M').
    rewrite -Ht'''. by move=> /steps_truncate.
  Qed.

  Lemma steps_None_mono {x} k2 k1 : steps k1 x = None -> k1 <= k2 -> steps k2 x = None.
  Proof.
    elim: k2 k1 x.
    { move=> [|k1]; [done|lia]. }
    move=> k2 IH [|k1] x + ?; first done.
    rewrite (steps_plus 1 k1) (steps_plus 1 k2).
    move: (steps 1 x) => [y|]; last done.
    move=> /IH. apply. lia.
  Qed.

  Lemma steps_sync {k1 x k2 y} :
    steps (S k1) x = None -> steps (S k2) x = Some y -> steps k1 y = None.
  Proof.
    elim: k1 k2 x.
    { move=> k2 x. rewrite (steps_plus 1 k2). by move=> ->. }
    move=> k1 IH k2 x.
    rewrite (steps_plus 1 (S k1)) (steps_plus 1 k2).
    move: (steps 1 x) => [z|]; last done.
    move: k2 => [|k2].
    { by move=> /= <- [<-]. }
    move=> /IH H /H /(steps_None_mono (S k1)). apply. lia.
  Qed.

  Lemma inverse_simulation q t k :
    steps k ((encode_state q), (encode_tape (Vector.hd t))) = None ->
    exists q' t', TM.eval M q t q' t'.
  Proof.
    elim: k q t; first done.
    move=> k IH q t.
    move Hq: (TM.halt q) => [|].
    { move=> _. exists q, t. by apply: TM.eval_halt. }
    move: (Hq) => /simulation_step => /(_ (Vector.hd t)).
    move=> [k1].
    move Hk1: (steps (S k1) _) => [[q' t']|]; last done.
    move=> [] Hq't'.
    move: Hk1 => /steps_sync H /H{H} /steps_truncate.
    move E: (TM_step _) Hq't' => [q'' t''].
    move=> [] -> -> /steps_truncate /IH.
    move=> [q'''] [t'''] /TM_facts.TM_eval_iff [n Hn].
    exists q''', t'''. apply /TM_facts.TM_eval_iff. exists (S n).
    rewrite /= /TM_facts.haltConf Hq -Hn -E (Vector.eta t) /=.
    move: (Vector.tl t). by apply: Vector.case0.
  Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Undecidability.TM.Reductions.Arbitrary_to_Binary.

Theorem reduction :
  TM.HaltTM 1 ⪯ SBTM2_HALT.
Proof.
  apply: reduces_transitive. apply: Arbitrary_to_Binary.reduction.
  exists (fun '(M, t) =>
    existT _ (M' M) (encode_config M (TM_facts.mk_mconfig (TM.start M) t))).
  move=> [M t]. split.
  - move=> /simulation [k Hk]. exists k.
    by move: Hk => /steps_truncate.
  - by move=> [k] /steps_truncate /inverse_simulation.
Qed.

Print Assumptions reduction.
