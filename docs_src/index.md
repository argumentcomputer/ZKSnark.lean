---
title: Formalizing ZkSNARKs
---
# What is it about?

In this blueprint we formalize the knowledge soundness proof for various ZkSNARK protocols in the Lean 4 theorem prover. The outline for the proofs of knowledge soundness for BabySNARK and Groth 16 are based off Bolton Bailey's Lean 3 [library](https://github.com/BoltonBailey/formal-snarks-project/). 

The current progress is focused on the [BabySNARK](https://github.com/initc3/babySNARK) protocol, and some general lemmas that are used across BabySNARK and [Groth 16](https://eprint.iacr.org/2016/260.pdf). 

The next steps for the project include:

1. Formalization of knowledge soundness for the NOVA protocol
2. Verification of other specifications for these protocols: zero knowledge, and completeness.

The eventual goal will include a reference implementation for the protocols together with proofs of correctness, but all of this is still in the works!

Consider contributing by visiting the [repository](https://github.com/yatima-inc/ZKSnark.lean/), checking out any open issues, or filling in any sorries you may find.