(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany

  Description:    
    Theorem "pure_typable_intro_prenex" can be used to 
    introduce/eliminate closed assumption ∀..∀.s where s is simple.
    Theorem "pure_typable_intro_poly_arr_0_0" can be used to 
    introduce/eliminate the assumption 0 -> 0 [1].

  Related Work:
  [1] Wells, Joe B. "Typability and Type-Checking in the Second-Order lambda-Calculus are Equivalent and Undecidable." 
      Proceedings Ninth Annual IEEE Symposium on Logic In Computer Science. IEEE, 1994.
*)

Require Import List Lia Relation_Definitions Relation_Operators Operators_Properties.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts pure_term_facts term_facts typing_facts iipc2_facts pure_typing_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* (\_.M) N *)
Definition K' M N := pure_app (pure_abs (ren_pure_term S M)) N.

Lemma pure_typing_K'I {Gamma M N t}: 
  pure_typing Gamma M t -> pure_typable Gamma N -> pure_typing Gamma (K' M N) t. 
Proof.
  move=> HM [tN HtN]. apply: (pure_typing_pure_app_simpleI (s := tN)); last done.
  apply: pure_typing_pure_abs_simpleI. apply: pure_typing_ren_pure_term; [by eassumption | done].
Qed.

Lemma pure_typing_K'E {Gamma M N t} : pure_typing Gamma (K' M N) t -> 
  pure_typing Gamma M t /\ pure_typable Gamma N.
Proof.
  rewrite /K'.
  move=> /pure_typingE [n] [?] [?] [?] [+] [+] [H1C ->] => /pure_typingE'.
  move=> /(pure_typing_ren_pure_term_allfv_pure_term Nat.pred (Delta := (map (ren_poly_type (Nat.add n)) Gamma))).
  apply: unnest.
  { rewrite allfv_pure_term_ren_pure_term /=. by apply: allfv_pure_term_TrueI. }
  rewrite renRen_pure_term ren_pure_term_id.
  move=> /(pure_typing_contains H1C) /pure_typing_many_poly_absI HM.
  move=> /(pure_typing_ren_poly_type (fun x => x - n)) /pure_typableI HN.
  constructor; first done.
  congr pure_typable: HN. rewrite map_map. apply: map_id' => ?.
  rewrite ?poly_type_norm ren_poly_type_id' /=; by [|lia].
Qed.

Lemma pure_typable_K'I {Gamma M N}: 
  pure_typable Gamma M -> pure_typable Gamma N -> pure_typable Gamma (K' M N).
Proof. move=> [tM] ? ?. exists tM. by apply: pure_typing_K'I. Qed.

Lemma pure_typable_K'E {Gamma M N} : pure_typable Gamma (K' M N) -> 
  pure_typable Gamma M /\ pure_typable Gamma N.
Proof. by move=> [?] /pure_typing_K'E [/pure_typableI]. Qed.

Fixpoint leftmost_poly_var (t: poly_type) :=
  match t with
  | poly_var x => Some x
  | poly_arr s t => leftmost_poly_var s
  | poly_abs t => if leftmost_poly_var t is Some (S x) then Some x else None
  end.

Fixpoint leftmost_path_length (t: poly_type) :=
  match t with
  | poly_var x => 0
  | poly_arr s t => 1 + leftmost_path_length s
  | poly_abs t => leftmost_path_length t
  end.

Lemma leftmost_poly_var_ren_poly_type {ξ t} : 
  leftmost_poly_var (ren_poly_type ξ t) = omap ξ (leftmost_poly_var t).
Proof.
  elim: t ξ; [done | by move=> ? + ? _ ? /= => -> |].
  move=> t + ? /= => ->. case: (leftmost_poly_var t); [by case | done].
Qed.

Lemma leftmost_poly_var_subst_poly_type {σ t} : 
  leftmost_poly_var (subst_poly_type σ t) = obind (σ >> leftmost_poly_var) (leftmost_poly_var t).
Proof.
  elim: t σ; [done | by move=> ? + ? _ ? /= => -> |].
  move=> t + σ /= => ->. case: (leftmost_poly_var t); last done.
  move=> [|x] /=; first done.
  rewrite /funcomp /= leftmost_poly_var_ren_poly_type.
  by case: (leftmost_poly_var _).
Qed.

Lemma leftmost_poly_var_many_poly_abs {n t x} :
  leftmost_poly_var (many_poly_abs n t) = Some x <->
  leftmost_poly_var t = Some (n+x).
Proof.
  elim: n x; first done.
  move=> n /= IH x. have ->: S (n + x) = n + S x by lia.
  rewrite -IH. case: (leftmost_poly_var (many_poly_abs n t)); last done.
  move=> [|y]; first done. constructor; by move=> [->].
Qed.

Lemma leftmost_path_length_ren_poly_type {ξ t} :
  leftmost_path_length (ren_poly_type ξ t) = leftmost_path_length t.
Proof.
  elim: t ξ; [done | by move=> ? + ? _ ? /= => -> |].
  move=> t + ? /= => ->. case: (leftmost_poly_var t); [by case | done].
Qed.

Lemma leftmost_path_length_subst_poly_type {σ t} :
  leftmost_path_length (subst_poly_type σ t) = 
  (if leftmost_poly_var t is Some x then leftmost_path_length (σ x) else 0) +
    leftmost_path_length t.
Proof.
  elim: t σ; [done | by move=> ? + ? _ ? /= => -> |].
  move=> t + σ /= => ->. case: (leftmost_poly_var t); last done.
  move=> [|x] /=; first done.
  by rewrite /funcomp /= leftmost_path_length_ren_poly_type.
Qed.

Lemma leftmost_path_length_many_poly_abs {n t} : 
  leftmost_path_length (many_poly_abs n t) = leftmost_path_length t.
Proof. by elim: n. Qed.

(* if type is not left-extensible, then leftmost_path_length is invarant under contains *)
Lemma contains_leftmost_path_length_eq {n s t} : 
  contains (many_poly_abs n s) t ->
  not (is_poly_abs s) ->
  match leftmost_poly_var s with
  | None => leftmost_path_length s = leftmost_path_length t
  | Some x => n <= x -> leftmost_path_length s = leftmost_path_length t
  end.
Proof.
  move Es': (many_poly_abs n s) => s' /clos_rt_rt1n_iff Hs't.
  elim: Hs't n s Es'.
  - move=> > <- _. rewrite ?leftmost_path_length_many_poly_abs. 
    by case: (leftmost_poly_var _).
  - move=> > [] r > _ IH [|n]; first by case=> /=.
    move=> s [?]. subst. evar (s'' : poly_type).
    have := IH n s''. rewrite subst_poly_type_many_poly_abs.
    subst s'' => /(_ ltac:(done)).
    move: s {IH} => [x | s {}t | /=]; last done.
    + move=> /= + _ ?.
      have ->: x = n + (1 + (x - n - 1)) by lia.
      rewrite ?iter_up_poly_type_poly_type ?leftmost_poly_var_ren_poly_type 
          ?leftmost_path_length_ren_poly_type /=.
      apply; by [|lia].
    + move=> /(_ ltac:(done)).
      rewrite leftmost_poly_var_subst_poly_type /=.
      move Eox: (leftmost_poly_var s) => ox. case: ox Eox.
      * move=> x Hsx /= + _ ?.
        rewrite leftmost_path_length_subst_poly_type Hsx.
        have ->: x = n + (1 + (x - n - 1)) by lia.
        rewrite ?iter_up_poly_type_poly_type ?leftmost_poly_var_ren_poly_type 
          ?leftmost_path_length_ren_poly_type /=.
        apply. by lia.
      * move=> /= Hs <- _. by rewrite leftmost_path_length_subst_poly_type Hs.
Qed.

(* self application is typed only by left-extensible types *)
Lemma pure_typable_self_application {Gamma x n t} : 
  not (is_poly_abs t) ->
  nth_error Gamma x = Some (many_poly_abs n t) ->
  pure_typable Gamma (pure_app (pure_var x) (pure_var x)) ->
  exists y, y < n /\ leftmost_poly_var t = Some y.
Proof.
  move=> Ht Hx /pure_typableE [?] [?] [].
  move=> /pure_typingE' [?] []. rewrite Hx => [[<-]] H1C.
  move=> /pure_typingE [n3] [?] [s'] [+] [].
  rewrite nth_error_map Hx => [[?]] H2C ?. subst.
  move: Ht H1C H2C. clear => Ht + /contains_ren_poly_type_addLR.
  move=> /contains_leftmost_path_length_eq + /contains_leftmost_path_length_eq.
  move=> /(_ Ht) + /(_ Ht).
  case: (leftmost_poly_var t).
  - move=> y H1y H2y. exists y. constructor; last done.
    suff: (not (n <= y)) by lia.
    move=> /copy [/H1y + /H2y] => -> /=.
    rewrite leftmost_path_length_many_poly_abs leftmost_path_length_ren_poly_type.
    by lia.
  - move=> -> /=.
    rewrite leftmost_path_length_many_poly_abs leftmost_path_length_ren_poly_type.
    by lia.
Qed.

Definition Mω := pure_abs (pure_app (pure_var 0) (pure_var 0)).

(* shape of types of \x.x x *)
Lemma pure_typing_Mω {Gamma t} : 
  pure_typing Gamma Mω t ->
  exists n1 n2 s' t' y, 
    t = many_poly_abs n1 (poly_arr (many_poly_abs n2 s') t') /\
    y < n2 /\ leftmost_poly_var s' = Some y.
Proof.
  rewrite /Mω. move=> /pure_typingE [n1] [s] [t'] [+ ->].
  have := many_poly_absI s. move=> [n] [s'] [->].
  move=> + /pure_typableI /pure_typable_self_application.
  move=> + H => /H /= => /(_ _ ltac:(done)) [y] [? ?].
  by exists n1, n, s', t', y.
Qed.

(* \x. K x (K (\w.(x (x w))) N)
  N can be used to work further with x *)
Definition M_Wells N := 
  pure_abs (K' (pure_var 0) (K' (pure_abs (pure_app (pure_var 1) (pure_app (pure_var 1) (pure_var 0)))) N)).

(* (\y. K (y y) (y Mω)) (M_Wells N) *)
Definition M_Wells_J N := pure_app 
  (pure_abs (K' (pure_app (pure_var 0) (pure_var 0)) (pure_app (pure_var 0) Mω)))
  (M_Wells N).

(* TODO maybe deprecate ? *)
Lemma leftmost_poly_var_contains_poly_arr {s x s' t'} : 
  leftmost_poly_var s = Some x ->
  contains s (poly_arr s' t') ->
  exists n'' s'' t'', s = many_poly_abs n'' (poly_arr s'' t'').
Proof.
  have [n'' [s'' [?]]] := many_poly_absI s. subst.
  case Es'': (s''); [ move=> _ | by move=> *; do 3 eexists | by move=> /=].
  rewrite leftmost_poly_var_many_poly_abs /=.
  move=> [?]. subst => /contains_tidyI.
  rewrite tidy_many_poly_abs_le /=; first by lia.
  by move=> /containsE.
Qed.

Lemma pure_typable_pure_app_0_Mω {n1 n2 s x t1 t2 Gamma} : 
  leftmost_poly_var s = Some (n2 + x) ->
  pure_typable
    (many_poly_abs n1 (poly_arr (many_poly_abs n2 (poly_arr s t1)) t2) :: Gamma)
    (pure_app (pure_var 0) Mω) ->
  exists n, s = many_poly_abs n (poly_var (n + (n2 + x))).
Proof.
  move=> H /pure_typableE [?] [?] [/pure_typingE'] [?] [[<-]].
  move=> /contains_many_poly_absE [?] [?].
  set σ := (fold_right _ _ _). rewrite subst_poly_type_many_poly_abs /=.
  set n := (_ - length _). case Hn: (n); last done. subst n.
  move=> [? ?]. subst => /pure_typing_Mω [?] [?] [?] [?] [?] [+] [?].
  rewrite subst_poly_type_many_poly_abs /=.
  move=> /many_poly_abs_eqE' [?] [+ ?]. subst.
  have [n' [s' [?]]] := many_poly_absI s. subst.
  case Es': (s'); [ | | by move=> /=].
  - subst => _. move: H. rewrite leftmost_poly_var_many_poly_abs /=.
    move=> [?]. subst => *. by eexists.
  - rewrite subst_poly_type_many_poly_abs /=.
    move=> _ /esym /many_poly_abs_eqE'' => /(_ ltac:(done)) [?] [?] ?. subst.
    move: H. rewrite ?leftmost_poly_var_many_poly_abs /= leftmost_poly_var_subst_poly_type.
    move=> ->. rewrite /= ?iter_up_poly_type_poly_type ?leftmost_poly_var_ren_poly_type.
    case: (leftmost_poly_var _); last done.
    move=> ? /= []. by lia.
Qed.

Lemma pure_typable_pure_app_0_0' {n1 n2 n3 n4 x y n5 s t Gamma}: 
  pure_typable
    (many_poly_abs n1
      (poly_arr
          (many_poly_abs n2
            (poly_arr (many_poly_abs n3 (poly_var (n3 + (n2 + x)))) (many_poly_abs n4 (poly_var y))))
          (many_poly_abs n5 (poly_arr s t))) :: Gamma)
    (pure_app (pure_var 0) (pure_var 0)) ->
  exists y', y = n4 + (n2 + y').
Proof.
  move=> /pure_typableE [?] [?] [/pure_typingE'] [?] [[?]] H1c. subst.
  move=> /pure_typingE [n6] [?] [?] [[?]] [H2c ?]. subst.
  move: H1c => /contains_poly_arrE [?] [?] /= [+ ?]. subst.
  set σ := (fold_right _ _ _).
  rewrite subst_poly_type_many_poly_abs /=.
  move=> /many_poly_abs_eqE'' => /(_ ltac:(done)) [n7] [? ?]. subst.
  move: H2c. rewrite ren_poly_type_many_poly_abs /=.
  move=> /contains_sub' [_].
  rewrite ren_poly_type_many_poly_abs /= many_poly_abs_many_poly_abs.
  move=> /contains_sub [?] [?] [?] [+] _.
  rewrite subst_poly_type_many_poly_abs /= many_poly_abs_many_poly_abs.
  move=> /many_poly_abs_eqE'' => /(_ ltac:(done)) [n8] [+ ?]. subst.
  have [?|?] : y < n4 + n6 + n7 \/ n4 + n6 + n7 <= y by lia.
  - rewrite iter_plus iter_up_poly_type_poly_type_lt; first by lia.
    by case: n8.
  - move=> _. exists (y - n4 - n6 - n7). by lia.
Qed.

Theorem pure_typable_intro_poly_arr_0_0 M : { N | 
  forall Gamma,
    pure_typable (map tidy ((poly_arr (poly_var 0) (poly_var 0)) :: (map (ren_poly_type S) Gamma))) M <->
    pure_typable (map tidy Gamma) N }.
Proof.
  exists (M_Wells_J M) => Gamma. constructor.
  - pose tI := poly_arr (poly_var 0) (poly_var 0).
    move=> HM. rewrite /M_Wells_J. pose t0 := poly_arr tI tI. exists t0.
    apply: (pure_typing_pure_app_simpleI (s := poly_abs t0)).
    + apply: pure_typing_pure_abs_simpleI. apply: pure_typing_K'I.
      * apply: (pure_typing_pure_app_simpleI (s := t0)).
        ** apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
        ** apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
      * pose s0 := poly_arr (poly_abs (poly_var 0)) (poly_abs (poly_var 0)). exists s0.
        apply: (pure_typing_pure_app_simpleI (s := s0)).
        ** apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
        ** apply: pure_typing_pure_abs_simpleI.
           apply: (pure_typing_pure_app_simpleI (s := (poly_abs (poly_var 0)))).
           *** apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
           *** apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
    + rewrite /M_Wells. apply: (pure_typing_pure_abs 1).
      apply: pure_typing_K'I; first by apply: pure_typing_pure_var_simpleI.
      apply: pure_typable_K'I.
      * exists tI. apply: pure_typing_pure_abs_simpleI. 
        apply: pure_typing_pure_app_simpleI; first by apply: pure_typing_pure_var_simpleI.
        apply: pure_typing_pure_app_simpleI; by apply: pure_typing_pure_var_simpleI.
      * move: HM. rewrite /= ?map_map. congr pure_typable. congr cons.
        apply: map_ext => ?. by rewrite tidy_ren_poly_type.
  - rewrite /M_Wells_J. move=> /pure_typableE [s] [?] [].
    move=> /pure_typingE' /pure_typableI /pure_typable_K'E [].
    have [ns [s' [? Hs]]] := many_poly_absI s. subst s. rename s' into s.
    move=> /copy [H00] /pure_typable_self_application => /(_ _ _ ltac:(eassumption) ltac:(done)).
    move=> [y [Hyns Hsy]] H. rewrite /M_Wells.
    move=> /pure_typingE [nM] [?] [?] [+ /many_poly_abs_eqE'].
    case Es: (s); [by move=> + [] | | by subst s].
    clear Hs => + [?] [? ?]. subst.
    move=> /pure_typing_K'E [] /pure_typingE [?] [?] [?] [[?]] [H1c ?]. subst.
    move=> /pure_typable_K'E [/pure_typableE] [?] /pure_typableE [?] [?] [].
    move=> /pure_typingE' [?] [[?]] H2c. subst.
    move=> /pure_typingE [?] [?] [?] [?] [+] [_] [H3c ?]. subst.
    move=> /pure_typingE' [?] [[?]] H4c HM. subst.
    move: (Hsy) => /= /leftmost_poly_var_contains_poly_arr => /(_ _ _ ltac:(eassumption)).
    move=> [?] [?] [?] ?. subst.

    move: Hsy. rewrite /= leftmost_poly_var_many_poly_abs /=. 
    move: H => /pure_typable_pure_app_0_Mω H /H{H} [? ?]. subst.
    
    move: H2c => /contains_poly_arrE [?] [?] [+ ?]. subst.
    rewrite subst_poly_type_many_poly_abs /= iter_up_poly_type_poly_type.
    rewrite fold_right_length_ts ?iter_up_poly_type_poly_type /=.
    move=> /many_poly_abs_eqE'' => /(_ ltac:(done)) [?] [? ?]. subst.

    move: H4c. rewrite ren_poly_type_many_poly_abs /=.
    move=> /contains_poly_arrE [?] [?] [? ?]. subst.

    move: (H3c) => /contains_tidyI. rewrite tidy_many_poly_abs_le /=; first by lia.
    move=> /contains_poly_varE [?] [?].
    set t := (t in ren_poly_type _ t).
    have [nt' [t' [?]]] := many_poly_absI t. subst t. subst.
    case Et': (t'); [move=> _ | move=> _ | by subst t'; move=> /= ].
    + subst t'.
      move: (H1c). rewrite ren_poly_type_many_poly_abs /=.
      move=> /contains_sub [?] [?] [?] [?] _. subst.
      move: H00. rewrite many_poly_abs_many_poly_abs.
      move=> /pure_typable_pure_app_0_0' [y' ?] _. subst.

      move: H3c => /contains_tidyI. rewrite tidy_many_poly_abs_le /=; first by lia.
      rewrite tidy_subst_poly_type tidy_ren_poly_type tidy_many_poly_abs_le /=; first by lia.

      rewrite iter_up_ren_ge; first by lia.
      rewrite fold_right_length_ts_ge /=; first by lia.
      move=> /containsE [?]. have ? : y = y' by lia. subst.

      move: HM => [?] /pure_typing_tidyI /=.
      rewrite tidy_many_poly_abs_le /=.
      { rewrite ?allfv_poly_type_many_poly_abs /= ?iter_scons_ge; by lia. }
      rewrite tidy_many_poly_abs_le /=; first by lia.
      rewrite tidy_many_poly_abs_le /=; first by lia.

      move=> /(pure_typing_ren_poly_type (fun x => x - (nM - 1))) /= /pure_typableI.
      congr pure_typable. congr cons.
      * congr poly_arr; congr poly_var; by lia.
      * rewrite ?map_map. apply: map_ext => ?.
        rewrite ?tidy_ren_poly_type tidy_tidy ?poly_type_norm /=.
        apply: extRen_poly_type. by lia.
    + rewrite ren_poly_type_many_poly_abs subst_poly_type_many_poly_abs /=.
      rewrite (svalP tidy_many_poly_abs). 
      by move: (sval _) => [? ?] /many_poly_abs_eqE' /= [].
Qed.

(* ∀.0 can be freely introduced/eliminated for typability *)
Theorem pure_typable_intro_poly_bot M : { N | 
  forall Gamma,
    pure_typable (map tidy ((poly_abs (poly_var 0)) :: Gamma)) M <->
    pure_typable (map tidy Gamma) N }.
Proof.
  exists (pure_abs M) => Gamma. constructor.
  - by move=> [tM] /= /pure_typing_pure_abs_simpleI /pure_typableI.
  - move=> /pure_typableE [s] [t] HM /=. exists t.
    apply: (pure_typing_weaken_closed (s' := s) (Gamma1 := [])); [done | | done].
    apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
Qed.

(* introduces a fresh type variable into environment, showing overall tools *)
Theorem pure_typable_intro_poly_var_0 M : { N | 
  forall Gamma,
    pure_typable (map tidy (poly_var 0 :: poly_arr (poly_var 0) (poly_var 0) :: (map (ren_poly_type S) Gamma))) M <->
    pure_typable (map tidy Gamma) N }.
Proof.
  (* (\x.M) (z y) where y : a -> a and z : ⊥ *)
  pose N := pure_app (ren_pure_term S (pure_abs M)) (pure_app (pure_var 1) (pure_var 0)).
  have [N' HN'] := pure_typable_intro_poly_bot N.
  have [N'' HN''] := pure_typable_intro_poly_arr_0_0 N'.
  exists N'' => Gamma. constructor.
  (* if M is typable, then so is N'' *)
  - move=> [tM] HtM. apply /HN'' /HN' {HN'' HN'}.
    eexists. apply: (pure_typing_pure_app_simpleI (s := poly_var 0)).
    + move=> /=. apply: pure_typing_pure_abs_simpleI.
      apply: pure_typing_ren_pure_term; first by eassumption. by case.
    + apply: (pure_typing_pure_app_simpleI (s := poly_var 0)).
      * by apply: pure_typing_pure_var_simpleI.
      * apply: (pure_typing_pure_var 0); first by reflexivity.
        by apply /rt_step /(contains_step_subst (s := poly_var 0)).
  - move /HN'' /HN' {HN'' HN'}. rewrite /N.
    move=> /pure_typableE [?] [?] [] /= /pure_typingE' HM.
    move=> /pure_typingE [n3] [?] [?] [?] [+] [+] [H2C ?]. subst.
    move=> /pure_typingE' [?] [[?]] H3C _. subst.
    move: H3C => /containsE [H1E ?]. subst.
    move: H2C => /containsE ?. subst.
    (* eliminate assumptions a -> a and ⊥ from HM *)
    move: HM => /=.
    set s := (s in pure_typing (s :: _) _ _).
    set Gamma' := (Gamma' in pure_typing (s :: _ :: Gamma') _ _).
    
    move=> /(pure_typing_ren_pure_term_allfv_pure_term (scons 0 (scons 1 S)) (Delta := s :: Gamma')).
    apply: unnest.
    { rewrite allfv_pure_term_ren_pure_term /=. apply: allfv_pure_term_TrueI. by case. } 
    rewrite renRen_pure_term /= ren_pure_term_id'; first by case.
    subst s Gamma'.
    move=> /pure_typing_tidyI /=. rewrite tidy_many_poly_abs_le /=; first by lia.
    move=> /pure_typableI.
    congr pure_typable. congr cons; last congr cons.
    + congr poly_var. by lia.
    + rewrite ?map_map. apply: map_ext => ?. by rewrite tidy_tidy.
Qed.

Ltac first_pure_typingE :=
  match goal with 
  | |- pure_typing _ (pure_app _ _) (poly_var _) -> _  =>
    move=> /pure_typingE' [?] [?] [+] [+] ?
  | |- pure_typing _ (pure_app _ _) (poly_arr _ _) -> _ => 
    move=> /pure_typingE' [?] [?] [+] [+] ?
  | |- pure_typing _ (pure_app _ _) _ -> _ => 
    move=> /pure_typingE [?] [?] [?] [?] [+] [+] [? ?]
  | |- pure_typing _ (pure_abs _) (poly_arr _ _) -> _ =>
    move=> /pure_typingE'
  | |- pure_typing _ (pure_abs _) _ -> _ =>
    move=> /pure_typingE [?] [?] [?] [+ ?]
  | |- pure_typing _ (pure_var _) (poly_var _) -> _ =>
    move=> /pure_typingE' [?] [[?]] ?
  | |- pure_typing _ (pure_var _) (poly_arr _ _) -> _ =>
    move=> /pure_typingE' [?] [[?]] ?
  | |- pure_typing _ (pure_var _) _ -> _ =>
    move=> /pure_typingE [?] [?] [?] [[?]] [? ?]
  | |- pure_typing _ (K' _ _) _ -> _ =>
    move=> /pure_typing_K'E []
  | |- pure_typable _ (K' _ _) -> _ =>
    move=> /pure_typable_K'E []
  | |- pure_typable _ (pure_var _) -> _ =>
    move=> _
  | |- pure_typable _ (pure_app _ _) -> _ =>
    move=> /pure_typableE [?] [?] []
  | |- pure_typable _ (pure_abs _) -> _ =>
    move=> /pure_typableE [?]
  end.

Ltac simplify_poly_type_eqs :=
  match goal with 
    | H : contains (poly_var _) _ |- _ => 
      move: H => /containsE ?
    | H : contains (poly_arr _ _) _ |- _ => 
      move: H => /containsE ?
    | H : contains (many_poly_abs _ (poly_arr _ _)) (poly_arr _ _) |- _ =>
      move: H => /contains_poly_arrE [?] [?] [? ?]
    | H : contains (subst_poly_type (fold_right scons poly_var _) _) _ |- _ =>
      move /contains_subst_poly_type_fold_rightE in H; rewrite ?many_poly_abs_many_poly_abs in H
    | H : many_poly_abs _ (poly_var _) = subst_poly_type _ _ |- _ =>
      move: H => /many_poly_abs_poly_var_eq_subst_poly_typeE => [[?]] [?] [?] [? ?]
    | H : contains (ren_poly_type _ (ren_poly_type _ _)) _ |- _ =>
      rewrite ?renRen_poly_type /= in H
    | H : contains (ren_poly_type _ (many_poly_abs ?n (poly_var (?n + _)))) _ |- _ => 
      rewrite ren_poly_type_many_poly_abs /= iter_up_ren in H
    | H : contains (ren_poly_type _ (many_poly_abs ?n (poly_arr (poly_var (?n + _)) (poly_var (?n + _))))) _ |- _ => 
      rewrite ren_poly_type_many_poly_abs /= ?iter_up_ren in H
    | H : contains (many_poly_abs ?n (poly_var (?n + _))) _ |- _ => 
      move: H => /contains_many_poly_abs_free [?] [?] [? ?]
    | H : poly_arr _ _ = many_poly_abs ?n _ |- _ => 
      (have ? : n = 0 by move : (n) H; case); subst n; rewrite /= in H
    | H : many_poly_abs ?n _ = poly_var _ |- _ => 
      (have ? : n = 0 by move : (n) H; case); subst n; rewrite /= in H
    | H : poly_var _ = poly_var _ |- _ => 
      move: H => [?]
  end.

Arguments funcomp {X Y Z} _ _ / _.

(* ∀a.∀b.a -> b -> b -> a *)
Definition poly_abba := poly_abs (poly_abs (poly_arr (poly_var 1) (poly_arr (poly_var 0) (poly_arr (poly_var 0) (poly_var 1))))).

Lemma contains_poly_abbaI {s t s' t'} : s' = s -> t' = t ->
  contains poly_abba (poly_arr s (poly_arr t (poly_arr t' s'))).
Proof.
  move=> -> ->. 
  apply: rt_trans; apply: rt_step; apply: contains_stepI; first done.
  by rewrite /= ?poly_type_norm subst_poly_type_poly_var.
Qed.

(* ∀a.∀b.a -> b -> b -> a can be freely introduced/eliminated for typability *)
Theorem pure_typing_intro_poly_abba M : { N | 
  forall Gamma,
    pure_typable (map tidy (poly_abba :: Gamma)) M <->
    pure_typable (map tidy Gamma) N }.
Proof.
  (* \f.\x.\y.\z. K x (K (f z) (f y)) *)
  pose N0 := (pure_abs (pure_abs (pure_abs (pure_abs (
    K' (pure_var 2) (K' 
      (pure_app (pure_var 3) (pure_var 0)) (pure_app (pure_var 3) (pure_var 1)))))))).
  (* \g. K (g x) (g y2 y1 y1 y1) where y1 : a, y2 : a -> a, and x : ⊥*)
  pose N1 := (pure_abs (K' (pure_app (pure_var 0) (pure_var 1)) 
    (many_pure_app (pure_var 0) [pure_var 3; pure_var 2; pure_var 2; pure_var 2]))).
  (* (\h.M) (N1 N0) *)
  pose N2 := pure_app (ren_pure_term (Nat.add 3) (pure_abs M)) (pure_app N1 N0).
  have [N2' HN2'] := pure_typable_intro_poly_bot N2.
  have [N2'' HN2''] := pure_typable_intro_poly_var_0 N2'.
  exists N2'' => Gamma. constructor.
  (* if M is typable, then so is N2'' *)
  - move=> [tM] HtM. apply /HN2'' /HN2' => {HN2'' HN2'}.
    eexists. apply: (pure_typing_pure_app_simpleI (s := poly_abba)).
    + move=> /=. apply: pure_typing_pure_abs_simpleI.
      move: HtM => /(pure_typing_ren_poly_type S) HtM.
      apply: pure_typing_ren_pure_term; first by eassumption.
      move=> [|]; first done.
      move=> ? ? /= <-. congr nth_error. rewrite ?map_map.
      apply: map_ext => ?. by rewrite tidy_ren_poly_type.
    + apply: (pure_typing_pure_app_simpleI
        (s := poly_abs (poly_abs (poly_arr (poly_arr (poly_var 0) (poly_var 0)) (poly_arr (poly_var 1) (poly_arr (poly_var 0) (poly_arr (poly_var 0) (poly_var 1)))))))).
      * apply: pure_typing_pure_abs_simpleI. apply: pure_typing_K'I.
        ** apply: (pure_typing_pure_app 2 (s := poly_arr (poly_var 0) (poly_var 0))).
           *** apply: (pure_typing_pure_var 0); first by reflexivity.
               apply: rt_trans; apply: rt_step; apply: contains_stepI; first done.
               by rewrite /= ?poly_type_norm subst_poly_type_poly_var.
           *** apply: (pure_typing_pure_var 0); first by reflexivity.
               constructor. by apply: contains_stepI.
           *** by apply: rt_refl.
        ** exists (poly_var 0). do 4 (apply: pure_typing_pure_app_simpleI; last by apply: pure_typing_pure_var_simpleI).
           move=> /=. apply: (pure_typing_pure_var 0); first by reflexivity.
           apply: rt_trans; apply: rt_step; apply: contains_stepI; first done.
           by rewrite /= ?poly_type_norm subst_poly_type_poly_var.
      * apply: (pure_typing_pure_abs 2). do 3 (apply: pure_typing_pure_abs_simpleI).
        apply: pure_typing_K'I; first by apply: pure_typing_pure_var_simpleI.
        exists (poly_var 0). apply: pure_typing_K'I;
          first by apply: pure_typing_pure_app_simpleI; apply: pure_typing_pure_var_simpleI.
        exists (poly_var 0). by apply: pure_typing_pure_app_simpleI; apply: pure_typing_pure_var_simpleI.
  (* if N2'' is typable, then so is M *)
  - move /HN2'' /HN2' => {HN2'' HN2'}. rewrite /N2 /N1 /N0 /= => {N2 N1 N0}.
    do ? first_pure_typingE. move=> HM.
    do ? first_pure_typingE. subst.
    do ? (simplify_poly_type_eqs; subst).

    do ? (match goal with H : many_poly_abs _ (poly_arr _ _) =  subst_poly_type _ _ |- _ => move: H end).
    move=> /many_poly_abs_poly_arr_eq_subst_poly_typeE [].
    { move=> [?] [? ?]. subst. do ? (simplify_poly_type_eqs; subst). done. }
    move=> [?] [?] [? ?]. subst.

    do ? (simplify_poly_type_eqs; subst).
    do 2 (match goal with H : _ = fold_right scons poly_var _ (length _ + _) |- _ => move: H end).
    do 2 (rewrite fold_right_length_ts_ge; first by lia).
    move=> ? ?. do ? (simplify_poly_type_eqs; subst).

    match goal with H : contains _ (poly_arr _ _) |- _ => move: H end.
    rewrite ren_poly_type_many_poly_abs /=.

    move=> /contains_poly_arrE [?] [?] [? ?]. subst.
    match goal with H : many_poly_abs _ _ = subst_poly_type _ _ |- _ => move: H end.
    rewrite ?poly_type_norm ?subst_poly_type_many_poly_abs /= ?iter_up_poly_type_poly_type.
    move=> /many_poly_abs_eqE'' /(_ ltac:(done)) [?] [? ?]. subst.
    do ? (simplify_poly_type_eqs; subst).

    move: HM => /=.
    (* eliminate superfluous assumptions from HM *)
    set s := (s in pure_typing (s :: _) _ _).
    set Gamma' := (Gamma' in pure_typing (s :: _ :: _ :: _ :: Gamma') _ _).
    
    move=> /(pure_typing_ren_pure_term_allfv_pure_term (scons 0 (scons 0 (scons 0 (scons 0 S)))) (Delta := s :: Gamma')).
    apply: unnest.
    { rewrite allfv_pure_term_ren_pure_term /=. apply: allfv_pure_term_TrueI. by case. }
    rewrite renRen_pure_term /= ren_pure_term_id'; first by case. subst Gamma'.

    (* weaken assumptions to abba *)
    have : pure_typing [poly_abba] (pure_var 0) (tidy s).
    {
      have Habba : [poly_abba] = map tidy [poly_abba] by done.
      rewrite /s {s}.
      rewrite Habba. apply: pure_typing_tidy_many_poly_abs_closed; first done.
      rewrite Habba. apply: pure_typing_many_poly_abs_contains_tidy_closed; [done | by eassumption |].
      rewrite Habba. apply: pure_typing_many_poly_abs_contains_tidy_closed; [done | by eassumption |].
      set ξ := (ξ in ren_poly_type ξ _). rewrite tidy_ren_poly_type.
      have ->: [poly_abba] = map (ren_poly_type ξ) [poly_abba] by done. apply: pure_typing_ren_poly_type.
      rewrite Habba. apply: pure_typing_tidy_many_poly_abs_closed; first done.
      rewrite /= tidy_many_poly_abs_le /=; first by lia.
      rewrite tidy_many_poly_abs_le /=.
      { do ? (rewrite ?allfv_poly_type_many_poly_abs /=).
        rewrite ?iter_scons ?iter_scons_ge; by lia. }
      rewrite tidy_many_poly_abs_le /=; first by lia.
      rewrite tidy_many_poly_abs_le /=.
      { do ? (rewrite ?allfv_poly_type_many_poly_abs /=).
        rewrite ?iter_scons ?iter_scons_ge; by lia. }
      rewrite tidy_many_poly_abs_le /=; first by lia.
      rewrite tidy_many_poly_abs_le /=; first by lia.
      
      apply: (pure_typing_pure_var 0); first done.
      apply: contains_poly_abbaI; congr poly_var; by lia.
    }
    move=> /pure_typing_weaken_closed => /(_ []) H /pure_typing_tidyI /= /H{H} => /(_ ltac:(done)).
    move=> /(pure_typing_ren_poly_type (Nat.pred)) /= /pure_typableI.
    congr pure_typable. congr cons. rewrite ?map_map. apply: map_ext => ?.
    by rewrite ?tidy_ren_poly_type tidy_tidy ?poly_type_norm ren_poly_type_id /=.
Qed.

(* 0 -> 1 ∼ e x0 x1  *)
Fixpoint trace_poly_type (e: nat) (t: poly_type) : pure_term :=
  match t with
  | poly_var x => pure_var x
  | poly_arr s t => pure_app (pure_app (pure_var e) (trace_poly_type e t)) (trace_poly_type e s)
  | poly_abs _ => pure_var 0
  end.

(* Module containing auxiliary lemmas for Theorem pure_typable_intro_prenex *)
Module pure_typable_intro_prenex_aux.

(* show that (g x .. x) where x : ⊥ is typed by (many_poly_abs n s) for pure_typable_intro_prenex *)
Lemma aux_pure_typing_gxs {Gamma x M n s} :
  nth_error Gamma x = Some (poly_abs (poly_var 0)) ->
  pure_typing Gamma M (Nat.iter n (fun s' : poly_type => poly_abs (poly_arr (poly_var 0) s')) s) ->
  pure_typing Gamma (many_pure_app M (repeat (pure_var x) n)) (many_poly_abs n s).
Proof.
  move=> Hx HM. apply: pure_typing_many_poly_absI.
  elim: n s HM; first by (move=> >; rewrite map_ren_poly_type_id).
  move=> n IH s.
  rewrite (ltac:(lia) : S n = n + 1) -repeat_appP many_pure_app_app /= => HM. 
  apply: (pure_typing_pure_app_simpleI (s := poly_var 0)).
  - have ->: map (ren_poly_type (Nat.add (n + 1))) Gamma =
      map (ren_poly_type S) (map (ren_poly_type (Nat.add n)) Gamma).
    { rewrite ?map_map. apply: map_ext => ?. rewrite poly_type_norm /=. by apply: extRen_poly_type; lia. }
    apply: (pure_typing_many_poly_absE (n := 1)). apply: IH.
    move: HM. by rewrite -iter_plus.
  - apply: (pure_typing_pure_var 0); first by rewrite ?nth_error_map Hx /=.
    by apply /rt_step /contains_step_subst.
Qed.

(* show that (g y .. y) where y : a is typable for pure_typable_intro_prenex *)
Lemma aux_pure_typable_gys {Gamma x M n s} : 
  nth_error Gamma x = Some (poly_var 0) ->
  pure_typing Gamma M (Nat.iter n (fun s' : poly_type => poly_abs (poly_arr (poly_var 0) s')) s) ->
  pure_typable Gamma (many_pure_app M (repeat (pure_var x) n)).
Proof.
  move=> Hx HM. exists (ren_poly_type (fun x => x - n) s). elim: n s HM.
  { move=> > /=. rewrite ren_poly_type_id'; by [|lia]. }
  move=> n IH s. rewrite (ltac:(lia) : S n = n + 1) -repeat_appP many_pure_app_app /=.
  rewrite -iter_plus /= => /IH /pure_typing_to_typing [?] [->] /=.
  move=> /(typing_ty_app (t := poly_var 0)) /= /(typing_app (Q := var x)).
  apply: unnest; first by apply: typing_var.
  move=> /typing_to_pure_typing /=. congr pure_typing.
  rewrite poly_type_norm ren_as_subst_poly_type /=. apply: ext_poly_type.
  case; first done. move=> ?. congr poly_var. by lia.
Qed.

Lemma aux_pure_typing_N0 {s n Gamma e }: 
  is_simple s ->
  allfv_poly_type (gt (n+e)) s ->
  allfv_poly_type (fun x => nth_error Gamma x = Some (poly_var x)) (many_poly_abs n s) ->
  nth_error Gamma e = Some poly_abba ->
  pure_typing Gamma (many_pure_term_abs n (trace_poly_type (n+e) s))
    (Nat.iter n (fun s' : poly_type => poly_abs (poly_arr (poly_var 0) s')) s).
Proof.
  move=> Hs. elim: n Gamma e.
  - move=> Gamma e /= _. elim: s Gamma Hs.
    + move=> /= *. by apply: pure_typing_pure_var_simpleI.
    + move=> s IHs t IHt Gamma /= [/IHs {}IHs /IHt {}IHt] [/IHs {}IHs /IHt {}IHt].
      move=> /copy [He] /copy [/IHs {}IHs /IHt {}IHt].
      apply: (pure_typing_pure_app_simpleI (s := s)); last done.
      apply: (pure_typing_pure_app 0 (s := t)); rewrite ?map_ren_poly_type_id; last by apply: rt_refl.
      * apply: (pure_typing_pure_var 0); [by rewrite nth_error_map He | ].
        apply: rt_trans; apply: rt_step.
        ** by apply: contains_stepI.
        ** apply: contains_stepI. by rewrite /= poly_type_norm /= subst_poly_type_poly_var.
      * done.
    + done.
  - move=> n IH Gamma e /= H1ns H2ns He. apply: (pure_typing_pure_abs 1).
    have ->: S (n + e) = n + S e by lia. apply: IH.
    + apply: allfv_poly_type_impl H1ns. by lia.
    + apply: allfv_poly_type_impl H2ns. case; first done.
      move=> ? /=. by rewrite nth_error_map => ->.
    + by rewrite /= nth_error_map He.
Qed.

Lemma pure_typing_many_pure_term_absE {Gamma n M t}:
  pure_typing Gamma (many_pure_term_abs n M) t ->
    exists (nss : list (nat * poly_type)) t', 
    n = length nss /\
    t = fold_right (fun '(n, s) r => many_poly_abs n (poly_arr s r)) t' nss /\
    pure_typing (fold_left (fun Gamma '(n, s) => s :: map (ren_poly_type (Nat.add n)) Gamma) nss Gamma) M t'.
Proof.
  elim: n Gamma t; first by move=> Gamma t /= HM; exists [], t.
  move=> n IH Gamma t /= /pure_typingE [n1] [s1] [t1] [+] ->.
  move=> /IH [nss] [t'] [->] [->] HM.
  by exists ((n1, s1) :: nss), t'.
Qed.

(* typing repeated application *)
Lemma pure_typing_fold_right_many_pure_app {Gamma x s' nss t M} :
  nth_error Gamma x = Some 
    (fold_right (fun '(n, s) r => many_poly_abs n (poly_arr s r)) s' nss) ->
  pure_typing 
    Gamma
    (many_pure_app (pure_var x) (repeat M (length nss))) t ->
  exists ns' ξ' nt' t', 
    t = many_poly_abs nt' t' /\ 
    contains (many_poly_abs ns' (ren_poly_type ξ' s')) t'.
Proof.
  rewrite -[Gamma in pure_typing Gamma _ _]map_ren_poly_type_id. move: (id) => ξ.
  elim /rev_ind: nss Gamma ξ s' t.
  - move=> Gamma ξ > Hx /= /pure_typingE [n1] [?] [?]. 
    rewrite ?map_map nth_error_map Hx => [[[<-]]].
    rewrite poly_type_norm /= => [[HC ->]].
    exists 0. do 3 eexists. constructor; [by reflexivity | by eassumption].
  - move=> [n s] nss IH /= Gamma ξ s' t.
    rewrite fold_right_app /= => /IH {}IH.
    rewrite app_length -repeat_appP many_pure_app_app /=.
    move=> /pure_typingE [n1] [?] [?] [?] [+] [_] [H1C ?]. subst.
    rewrite ?map_map. under map_ext => ? do rewrite poly_type_norm.
    move=> /IH [n1s'] [n2s'] [nt'] [t'] []. case: nt'; last done. move=> /= ?. subst.
    rewrite ren_poly_type_many_poly_abs many_poly_abs_many_poly_abs /=.
    move=> /contains_poly_arrE [?] [?] [? ?]. subst.
    move: H1C => /contains_subst_poly_type_fold_rightE.
    clear=> ?. do 4 eexists. constructor; [by reflexivity | by eassumption].
Qed.

Lemma pure_typable_many_pure_app_repeat_poly_var {Gamma x y ny nss t} :
  nth_error Gamma x = Some 
    (fold_right (fun '(n, s) r => many_poly_abs n (poly_arr s r)) t nss) ->
  nth_error Gamma y = Some (poly_var ny) ->
  pure_typable Gamma (many_pure_app (pure_var x) (repeat (pure_var y) (length nss))) ->
  Forall (fun '(_, s) => exists n x, s = many_poly_abs n (poly_var (n + x))) nss.
Proof.
  move=> + Hy. elim /rev_ind: nss t; first done.
  move=> [n s] nss IH t. rewrite fold_right_app /= => Hx.
  rewrite app_length -repeat_appP many_pure_app_app /=.
  move=> /pure_typableE [?] [?] [].
  move=> /copy [/pure_typableI /IH] /(_ _ Hx) Hnss.
  move=> /(pure_typing_fold_right_many_pure_app Hx) [?] [?] [[|?]] [?] []; last done.
  move=> /= ?. subst. rewrite ren_poly_type_many_poly_abs many_poly_abs_many_poly_abs /=.
  move=> /contains_poly_arrE [?] [?] [? ?]. subst.
  move=> /pure_typingE [?] [?] [?] [+] [+]. rewrite nth_error_map Hy => [[?]]. subst.
  rewrite poly_type_norm. move=> /containsE <-.
  move=> /esym /many_poly_abs_poly_var_eq_subst_poly_typeE [?] [?] [?] [? ->].
  apply /Forall_appP. constructor; first done.
  constructor; last done. clear.
  by do 2 eexists.
Qed.

Lemma pure_typing_trace_poly_typeE {s ns Gamma t n}: 
  is_simple s ->
  allfv_poly_type (gt (length ns)) s ->
  pure_typing 
    ((map (fun x => poly_var (n + x)) ns) ++ poly_abba :: Gamma) 
    (trace_poly_type (length ns) s) t -> 
  ren_poly_type (fun x => n + nth x ns 0) s = tidy t.
Proof.
  elim: s Gamma t n.
  - move=> x Gamma t n _ /= ? /pure_typingE [n1] [?] [?]. 
    rewrite ?nth_error_map nth_error_app1; first by rewrite map_length; lia.
    rewrite nth_error_map. 
    have -> := nth_error_nth' ns 0; first by lia.
    move: (nth x ns 0) => y [[?]] []. subst.
    move=> /containsE ? ->. subst.
    rewrite tidy_many_poly_abs_le /=; first by lia.
    congr poly_var. by lia.
  - move=> s1 IH1 s2 IH2 Gamma t n /= [/IH1 {}IH1 /IH2 {}IH2] [/IH1 {}IH1 /IH2 {}IH2].
    move=> /pure_typingE [n1] [?] [?] [?] [+] [+] [H1C ?]. subst.
    move=> /pure_typingE' [?] [?] [+] [+] H2C.
    move=> /pure_typingE' [?] [+] H3C.
    rewrite ?nth_error_map nth_error_app2; first by rewrite ?map_length; lia.
    rewrite ?map_length (ltac:(lia) : length ns - length ns = 0) /=.
    move=> [?]. subst. move: H3C => /(contains_poly_arrE (n := 2)) => - [[|r1 [|r2 [|? ?]]]] [] //=.
    move=> _ [? ?]. subst. move: H2C => /containsE [? ?]. subst.
    move: H1C => /containsE ?. subst.
    rewrite ?map_app /= ?map_map /=.
    under [map _ ns]map_ext => x do rewrite (ltac:(lia) : n1 + (n + x) = (n1 + n) + x). 
    move=> /IH2 {}IH2 /IH1 {}IH1. rewrite -tidy_many_poly_abs_tidy /= -IH1 -IH2.
    rewrite tidy_many_poly_abs_le /=.
    { rewrite ?allfv_poly_type_ren_poly_type /=. constructor; apply: allfv_poly_type_TrueI; by lia. } 
    rewrite IH1 IH2 ?tidy_tidy -IH1 -IH2 ?poly_type_norm /=.
    congr poly_arr; apply: extRen_poly_type; by lia.
  - done.
Qed.

End pure_typable_intro_prenex_aux.

Import pure_typable_intro_prenex_aux.

(* key Theorem that introduces closed assumption ∀..∀.s where s is simple *)
Theorem pure_typable_intro_prenex M s n : 
  is_simple s -> allfv_poly_type (gt n) s ->
  { N | 
    forall Gamma,
      pure_typable (map tidy (many_poly_abs n s :: Gamma)) M <->
      pure_typable (map tidy Gamma) N }.
Proof.
  move=> Hs Hns.
  (* \x_0..\x_{n-1}. trace_poly_type n s *)
  pose N0 := many_pure_term_abs n (trace_poly_type n s).
  (* \g. K (g x .. x) (g y .. y) where y : a and x : ⊥*)
  pose N1 := pure_abs (K' (many_pure_app (pure_var 0) (repeat (pure_var 2) n)) 
    (many_pure_app (pure_var 0) (repeat (pure_var 3) n))).
  (* (\h.M) (N1 N0) *)
  pose N2 := pure_app (ren_pure_term (Nat.add 4) (pure_abs M)) (pure_app N1 N0).
  have [N2_1 HN2_1]:= pure_typing_intro_poly_abba N2. (* introduce e : ∀a.∀b. a -> b -> b -> a *)
  have [N2_2 HN2_2] := pure_typable_intro_poly_bot N2_1. (* introduce x : ⊥ *)
  have [N2_3 HN2_3] := pure_typable_intro_poly_var_0 N2_2. (* introduce y : a and y' : a -> a *)
  exists N2_3 => Gamma. constructor.
  (* if M is typable, then so is HN2_3 *)
  - move=> [tM] HtM. apply /HN2_3 /HN2_2 /HN2_1 => {HN2_3 HN2_2 HN2_1}.
    eexists. apply: (pure_typing_pure_app_simpleI (s := tidy (many_poly_abs n s))).
    + move=> /=. apply: pure_typing_pure_abs_simpleI.
      move: HtM => /(pure_typing_ren_poly_type S) HtM.
      apply: pure_typing_ren_pure_term; first by eassumption. case.
      * move=> ? /= <-. rewrite -tidy_ren_poly_type. congr Some. congr tidy.
        rewrite ren_poly_type_allfv_id ?allfv_poly_type_many_poly_abs; last done.
        apply: allfv_poly_type_impl Hns => ? ?. rewrite iter_scons_lt; by [lia |].
      * move=> ? ? /= <-. congr nth_error. rewrite ?map_map.
        apply: map_ext => ?. by rewrite tidy_ren_poly_type.
    + apply: (pure_typing_pure_app_simpleI
        (s := tidy (Nat.iter n (fun s' => poly_abs (poly_arr (poly_var 0) s')) s))).
      * rewrite -/(tidy (poly_arr _ _)). apply: pure_typing_tidyI.
        apply: pure_typing_pure_abs_simpleI. apply: pure_typing_K'I.
        ** apply: aux_pure_typing_gxs; [done | by apply: pure_typing_pure_var_simpleI].
        ** apply: aux_pure_typable_gys; [done | by apply: pure_typing_pure_var_simpleI].
      * apply: pure_typing_tidyI. rewrite /N0.
        have ->: trace_poly_type n = trace_poly_type (n+0) by congr trace_poly_type; lia.
        apply: aux_pure_typing_N0; [done | by apply: allfv_poly_type_impl Hns; lia | | done].
        rewrite allfv_poly_type_many_poly_abs. apply: allfv_poly_type_impl Hns.
        move=> ? ?. rewrite iter_scons_lt; by [lia|].
  (* if HN2_3 is typable, then so is M *)
  - move /HN2_3 /HN2_2 /HN2_1 => {HN2_3 HN2_2 HN2_1}.
    rewrite /N2 /N1 /N0 /= => {N2_3 N2_2 N2_1}.
    move=> /pure_typableE [?] [?] [].
    move=> /pure_typingE' HM.
    move=> /pure_typingE [n3] [?] [?] [?] [+] [+] [H2C ?]. subst.
    move=> /pure_typingE'.
    move=> /pure_typing_K'E [HN1_1] HN1_2.
    move=> /pure_typing_many_pure_term_absE [nss] [?] [?] [?]. subst.
    (* inspect HN1_2, show that resulting type is essentially a renaming of s *)
    move: HN1_2 => /pure_typable_many_pure_app_repeat_poly_var.
    evar (r : poly_type) => /(_ (n3 + 0) r). apply: unnest; first by subst r.
    apply: unnest; first done.
    move=> Hnss. (* all types in nss are essentially poly_var _ *)
    set Gamma' := (Gamma' in pure_typing Gamma' _ _).
    have : exists ss Gamma'', length ss = length nss /\ 
      Gamma' = ss ++ poly_abba :: Gamma'' /\
      Forall (fun 's => exists n x, s = many_poly_abs n (poly_var (n + x))) ss.
    {
      rewrite /Gamma'. elim /rev_ind: (nss) Hnss; first by move=> ?; exists []; eexists.
      clear=> [[n s]] nss IH /Forall_appP [/IH] {}IH /Forall_singletonP [n0] [x0] ->.
      
      rewrite fold_left_app app_length.
      move: IH => [ss] [Gamma''] [<-] /= [->] Hss.
      eexists (_ :: map (ren_poly_type (Nat.add n)) ss), (map (ren_poly_type (Nat.add n)) Gamma'').
      rewrite /= map_length map_app /= Forall_consP Forall_mapP.
      constructor; first by lia.
      constructor; first done.
      constructor; first by do 2 eexists.
      apply: Forall_impl Hss => ? [?] [? ->]. rewrite ren_poly_type_many_poly_abs /= iter_up_ren.
      by do 2 eexists.
    }
    move=> [ss] [?] [H1ss] [-> {Gamma'}] H2ss. rewrite -H1ss.
    move=> /pure_typing_tidyI. rewrite map_app /=.
    have [ns [H1ns H2ns]] : exists ns, length ss = length ns /\ map tidy ss = map poly_var ns.
    {
      elim: (ss) H2ss; first by move=> _; exists [].
      clear=> s ss IH /Forall_consP [] [?] [n] -> /IH [ns] /= [-> ->].
      exists (n :: ns). constructor; first done.
      rewrite tidy_many_poly_abs_le /=; first by lia.
      congr cons. congr poly_var. by lia.
    }
    rewrite H1ns H2ns. move=> /(pure_typing_trace_poly_typeE (n := 0)).
    rewrite -H1ns H1ss tidy_tidy => /(_ ltac:(done) ltac:(done)).
    move: HN1_1 => /pure_typing_fold_right_many_pure_app /= => /(_ _ ltac:(done)).
    move=> [n6] [ξs] [n7] [?] [? H3C]. subst.

    (* eliminate superfluous assumptions from HM *)
    move=> H2s. move: HM => /=.
    set s0 := (s0 in pure_typing (s0 :: _) _ _).
    set Gamma0 := (Gamma0 in pure_typing (s0 :: _ :: _ :: _ :: _ :: Gamma0) _ _).

    move=> /(pure_typing_ren_pure_term_allfv_pure_term (scons 0 (scons 0 (scons 0 (scons 0 (scons 0 S))))) (Delta := s0 :: Gamma0)).
    apply: unnest.
    { rewrite allfv_pure_term_ren_pure_term /=. apply: allfv_pure_term_TrueI. by case. } 
    rewrite renRen_pure_term /= ren_pure_term_id'; first by case. subst Gamma0.
    have H4s : allfv_poly_type (fun=> False) (tidy (many_poly_abs (length nss) s)).
    {
      rewrite allfv_poly_type_tidy allfv_poly_type_many_poly_abs.
      apply: allfv_poly_type_impl Hns => ? ?. rewrite iter_scons_lt; by [|lia].
    }
    (* weaken first assumption to many_poly_abs (length nss) s *)
    have : pure_typing [tidy (many_poly_abs (length nss) s)] (pure_var 0) (tidy s0).
    {
      have H3s : [tidy (many_poly_abs (length nss) s)] = map tidy [tidy (many_poly_abs (length nss) s)] 
        by rewrite /= tidy_tidy.

      rewrite /s0 {s0}.
      rewrite H3s. apply: pure_typing_tidy_many_poly_abs_closed; first done.
      rewrite H3s. apply: pure_typing_many_poly_abs_contains_tidy_closed; [done | by eassumption |].
      rewrite H3s. apply: pure_typing_many_poly_abs_contains_tidy_closed; [done | by eassumption |].
      rewrite tidy_ren_poly_type -H2s ?poly_type_norm /=.
      rewrite -[s in ren_poly_type _ s](tidy_is_simple Hs) -tidy_ren_poly_type -/(map tidy [_]).
      apply: pure_typing_tidyI. apply: (pure_typing_pure_var 0); first done.
      rewrite ren_poly_type_id ren_as_subst_poly_type. by apply: contains_many_poly_abs_closedI. 
    }
    move=> /pure_typing_weaken_closed => /(_ []) H /pure_typing_tidyI /= /H{H} => /(_ ltac:(done)).
    move=> /(pure_typing_ren_poly_type (fun x => x - 1)) /= /pure_typableI.
    congr pure_typable. congr cons.
    + rewrite ren_poly_type_allfv_id; last done. by apply: allfv_poly_type_impl H4s.
    + rewrite ?map_map. apply: map_ext => ?.
      rewrite ?tidy_ren_poly_type tidy_tidy ?poly_type_norm /=.
      apply: ren_poly_type_id'. by lia.
Qed.
