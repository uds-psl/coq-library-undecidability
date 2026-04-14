# The undecidability of the logic BI of Bunched Implication

## Description of the contribution:

The question of the decidability or undecidability of [the logic of Bunched Implications](https://doi.org/10.2307/421090) (BI for short) has been a long standing issue within the proof theoretic community. The logic BI combines the linear fragment of intuitionistic linear logic w/o exponentials (ILL for short) and intuitionistic logic (IL for short), in an orthogonal way, i.e. it is conservative over both of these fragments.  

There have been several claims for the decidability for BI with some of these actually published. See this non exhaustive list:
- [_Semantic Labelled Tableaux for propositional BI (without bottom)_](https://doi.org/10.1093/logcom/13.5.707) Galmiche & Méry. Journal of Logic and Computation, 2003, 13 (5), pp.707-753.
- [_The semantics of BI and resource tableaux_](https://doi.org/10.1017/S0960129505004858) Galmiche, Méry & Pym. Mathematical Structures in Computer Science. 2005;15(6):1033-1088.
- [_A syntactic proof of decidability for the logic of bunched implication BI_](https://doi.org/10.48550/arXiv.1609.05847) Ramanayake. arXiv 2016.
- [_An Algebraic Glimpse at Bunched Implications and Separation Logic_](https://doi.org/10.1007/978-3-030-76920-8_5) Jipsen & Litak. In Outstanding Contributions to Logic, vol 23. Springer. 2022
- [_The Lambek Calculus Extended with Intuitionistic Propositional Logic_](https://doi.org/10.1007/s11225-016-9665-0) Kaminski & Francez. Stud Logica 104, 1051–1082 (2016).

Several syntactic proofs of decidability for  BI have also been attempted but more obvious flaws were discovered in those.
  
A first surprise came when the Boolean variant of the logic, called Boolean BI (BBI for short), with classical propositional logic CL for the additive part (as opposed to IL connectives for BI), has been proved __undecidable__, independently and simultaneously by:
- [1] [_Undecidability of propositional separation logic and its neighbours_](http://dx.doi.org/10.1109/LICS.2010.24) Brotherston & Kanovich. LICS 2010, pp. 130-139. 
- [2] [_The undecidability of boolean BI through phase semantics_](http://dx.doi.org/10.1109/LICS.2010.18) Larchey-Wendling & Galmiche. LICS 2010, pp. 140-149.

Indeed, at first, BBI was _naively_ considered less expressive than BI, because of the analogy with CL vs. IL. Hence that felt like an apparent contradiction with the then assumed "decidability" of BI.

The main part of the proof [2] of undecidability is actually my original motivation for this very library since it is based on the undecidability of the elementary fragment of intuitionistic linear logic EILL:
- [3] [_Certified undecidability of intuitionistic linear logic via binary stack machines and Minsky machines_](https://doi.org/10.1145/3293880.3294096) Forster & Larchey-Wendling. CPP 2019, pp. 104-117.

However, the reduction from EILL to BBI in [2] uses _trivial phase semantics_ which in turn requires _the law of excluded middle_ (XM) to be proved sound for BBI: as a Boolean logic, BBI validates its internal form of XM which then reflects at the meta-level of Rocq via trivial phase semantics in the identity `⟦A ∨ ¬ A⟧ x = ⟦A⟧ x ∨ ¬ ⟦A⟧ x`. 

So the end part `EILL ⪯ BBI`  of the reduction chain of [2] could not be integrated into the framework of synthetic undecidability in [3]. The synthetic approach to undecidability (or decidability) does not mix well with axioms, in particular not computable ones like XM. So to get `EILL ⪯ BBI`, we would possibly need an alternate semantics for BBI that is sound w/o assuming XM at the meta-level (possibly general phase semantics ?).

Back to (intuitionistic) BI, it turns out that all those claims of decidability for (intuitionistic) BI were faulty after all, thanks to a new _remarkable contribution_:
 - [4] [_The logic of bunched implications is undecidable_](https://doi.org/10.48550/arXiv.2603.01595) Galatos, Jipsen, _Knudstorp_ & Ramanayake. arXiv 2026

the original breakthrough actually coming from Knudstorp (as far as I understand). Two proofs are actually proposed in [4]:
1. one from tilling problems (complicated)
2. one from acceptance for 2 counters And branching Minsky machines `ACM2` [5] (much simpler)
 
Tilling problems are currently unavailable in the Coq library of undecidability proofs. 

So, in the spirit of the reduction from `MM` to `EILL` in [3], we implement a positive encoding of `ACM2`, and contrary to the negative encoding of `ACM2` contained in [4], we do not require XM to show correctness of the reduction. The main novelty comes from the simulation of dereliction rule in BI as proposed in [4] above, encoding the relativized exponentional `![γ]φ` with `(⊤-∗((φ-∗γ)→γ))∧1` and allowing to show both:
```coq
           Γ ⊦ ψ                                Γ, ![γ]φ, φ ⊦ γ
      -------------- (weakening)              ------------------ (dereliction)
       Γ, ![γ]φ ⊦ ψ                              Γ, ![γ]φ ⊦ γ
```

Notice that dereliction `!φ,φ ↠ !φ` is a consequence of the contraction rule `!φ,!φ ↠ !φ` of linear logic, but it is __ENOUGH__ to encode `ACM2` because it allows to __copy__ an instruction from the program store to the computational context. While possible in BBI with the simple encoding `!φ := φ∧1` (see [2]), it is unknown whether general contraction `!φ,!φ ↠ !φ` can be encoded into BI.

We start from the seed `ACM2` [5] which we first need to establish undecidable by reduction from `ndMM2`
(two counters non deterministic Minsky machines). 

## Implementation:

Seed problem used:
- `ndMM2_ACCEPT`: acceptance for two counters non-deterministic Minsky machines (with an unbounded number of locations for instructions)

New problems:
- `ACM2_ACCEPT`: acceptance for two-counters _And branching Minsky machines_ (with an unbounded number of locations for instructions), called 2-ACM in [4] or [5] (see below).
- `BI_SEQ_PROVABLE`: cut-free provability for a parameterized fragment of BI:
  - choice of available connectives and the respecting left/right sequent rules
  - choice to include the _cut rule_ or not
- `BI_HILBERT_PROVABLE`: provability using a Hilbert style proof system for the full fragment of BI
  
Reductions:
- `ndMM2_ACCEPT ⪯ ACM2_ACCEPT`;
- `ACM2_ACCEPT ⪯ BI_SEQ_PROVABLE` for any fragment containing : 
  - `-∗` (magic wand, linear implication)
  - `1` (multiplicative unit)
  - `→` (intuitionistic implication)
  -  `∧` (additive conjunction),
-  `ACM2_ACCEPT ⪯ BI_HILBERT_PROVABLE` 

## References:
- [5] [_Decision problems for propositional linear logic_](https://doi.org/10.1016/0168-0072(92)90075-B) Lincoln, Mitchell, Scedrov & Shankar
       Annals of Pure and Applied Logic 56 (1992) 239-311
