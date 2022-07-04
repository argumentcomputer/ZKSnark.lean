# zkSNARKs for lean

## Goals of the project

The main goals for this project are to port some of the contents of the [formal-snarks-project](https://github.com/BoltonBailey/formal-snarks-project/) repository to Lean 4, and implement a formalization for other Zk SNARK protocols.

In particular in this repository we will

* Port the general lemmas and aspects of mathlib that are needed
* Port the verification for knowledge soundness of the [BabySNARK](https://github.com/initc3/babySNARK/blob/master/babysnark.pdf) protocol
* Do the same for the [Groth16](https://eprint.iacr.org/2016/260.pdf) protocol
* Verify for the first time knowledge soundness for the [NOVA](https://eprint.iacr.org/2021/370.pdf) protocol. 

## Contributing

There are two big aspects to this work: the formalization and documentation.

### Formalization

The formalization can be found in the [`ZkSNARK`](/ZkSNARK/) folder. As the project matures, there will likely be more structure to this aspect.

### Documentation

Contributing to the documentation can be done by editing the `.tex` files in the [blueprint](blueprint/src/content) folder. 

The blueprint is automatically generated from the links and references used in the `.tex` files in this contained folder. All lemmas, definitions, theorems, chapters, sections, etc. should be labeled.

In particular, `lemma`s, `definition`s, and `theorem`s will appear as nodes in the directed graph, and adding a `\uses{...}` tag in the proof of a `lemma` or `theorem` will add a directed edge to indicate the dependence. 

Including `\leanok` in the statement will indicate in the blueprint graph that the definition has been implemented in lean, and adding `\leanok` to the proof will indicate that the proof has been formalized (by filling in the oval with green). 

## Building the blueprint

It should not be necessary for anyone to have to rebuild the blueprint locally, as there is a Github workflow set up in this repository to rebuild the blueprint on every push to `main`. 

If for some reason you want to test your changes locally follow the following steps (adapted from the Lean 3 project https://github.com/b-mehta/unit-fractions/):

Building the blueprint requires `graphviz` and `libgraphviz-dev` which can be obtained on Debian based distros with 

```
sudo apt install graphviz libgraphviz-dev
```

The build also has a few Python dependencies

```
pip3 install invoke pandoc
``` 

Finally, the blueprint is built using a Python LaTeX compiler called [plasTeX](https://github.com/plastex/plastex/) together with the `noleanblueprint` plugin: 

```
git clone https://github.com/plastex/plastex
pip3 install ./plastex
git clone https://github.com/mpenciak/noleanblueprint
pip3 install ./noleanblueprint
```

The `noleanblueprint` is a fork of the original [leanblueprint](https://github.com/PatrickMassot/leanblueprint) plasTeX plugin which was originally written to help organize Lean 3 formalization projects. The fork simply gets rid of the Lean 3 specific aspects of the original. 

At the root of the project directory 
```
inv all
``` 
should build the blueprint and 
```
inv serve
```
will create a local host for the generated website at `http://localhost:8000/`

## Using mathport

This Lean package has [mathlib3port](https://github.com/leanprover-community/mathlib3port.git) as a dependency. 

The effect of this is that we can use Lean 4 `.olean`s which have been translated from Lean 3 compiled [mathlib](https://github.com/leanprover-community/mathlib). Check out the example [mathporttest.lean](mathporttest.lean) for usage.  

Furthermore, we can also look at the syntactically generated Lean 4 `.lean` files by jumping to definitions. The `synport` generated files almost certainly do not compile, but can still be used to cross-reference definitions and statements without having to keep a separate copy of Lean 3 open. 