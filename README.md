System E: A Formal System for Euclid's Elements
--------------------------------

System E [1] is a logic system designed for formalizing the theorems and proofs in Book I to IV of *Euclid's Elements of Geometry*. This repo is an implementation of a variant of System E. It encodes Euclid's proofs in Coq and uses Z3 for filling in the reasoning jumps in the proofs (referred to as "direct consequences" in the original System E paper).

[1]
```
@article{avigad2009formal,
  title={A formal system for Euclid’s Elements},
  author={Avigad, Jeremy and Dean, Edward and Mumma, John},
  journal={The Review of Symbolic Logic},
  volume={2},
  number={4},
  pages={700--768},
  year={2009},
  publisher={Cambridge University Press}
}
```

## Dependencies

* [OPAM](https://opam.ocaml.org/)
* [Coq == 8.9.1](https://opam.ocaml.org/packages/coq/) install via OPAM: `opam install coq=8.9.1`
* [dune == 1.10.0](https://opam.ocaml.org/packages/dune/) install via OPAM: `opam install dune=1.10.0`
* [z3 == 4.8.1](https://opam.ocaml.org/packages/z3/z3.4.8.1/) install via OPAM: `opam install z3=4.8.1`

*Note*: Please install the exact versions listed above, as there are known issues with z3 4.8.4 and dune 1.11.

## Installation

1. `export LD_LIBRARY_PATH=/n/fs/grad/kaiyuy/.opam/4.07.1+flambda/lib/z3:$LD_LIBRARY_PATH`
2. `dune build && dune install`


## Running

`coqc Book_1.v`


## Example Proof

This is a formalized proof of Proposition 1 in Book I.

```coq
Theorem Proposition_1 : forall (a b : Point), a <> b ->
    exists c : Point, (SegmentPP c a == SegmentPP a b)%segment /\ (SegmentPP c b == SegmentPP a b)%segment.
Proof.
    intros.
    euclid_apply (ConstructionRules.circle_from_points a b) as alpha. (* construct a circle centered around a *)
    euclid_apply (ConstructionRules.circle_from_points b a) as beta. (* construct a circle centered around b *)
    euclid_apply (ConstructionRules.intersection_circles alpha beta) as c.  (* construct the intersection c between two circles *)
    exists c.
    euclid_apply (TransferInferences.point_on_circle_onlyif a b c alpha).  (* deduce ac = ab *)
    euclid_apply (TransferInferences.point_on_circle_onlyif b a c beta).  (* deduce bc = ba *) 
    (* metric inferences *)
    euclid_apply (MetricInferences.segment_symm a c).
    euclid_apply (MetricInferences.segment_symm b c).
    euclid_apply (MetricInferences.segment_symm a b).
    lra. 
Qed.

```
