# Leo-III-lambdapi-lib

This repository contains encodings of various inference rules and meta-theorems used in the verification of the Higher-Order Logic Automated Theorem Prover **Leo-III** [1] within the **Dedukti** framework [2]. These encodings are developed with the interactive proof assistant **Lambdapi** [3]. The version of Leo-III that outputs Lambdapi proofs is currently being developed and can be found online [4].

> **Note:**  
> Many encodings that were originally part of this library have been integrated into the Lambdapi **standard library** [5]. This includes axioms for functional and propositional extensionality (now in the standard library files `FunExt.lp` and `PropExt.lp`), as well as theorems for simplification, literal transformations, and several list encodings and theorems for literal-level operations such as permutation (now in the standard library files `Disj.lp` and `Conj.lp`).

## Included Files

- **`CNF.lp`**  
  Experimental encoding of a clausification procedure relying on proof by reflection. Not yet used by the implementation.

- **`CNFeq.lp`**  
  Encoding of the rules used in the clausification procedure of Leo-III as equalities. Used with the rewrite tactic in the current implementation.
  
- **`EPrules.lp`**  
  Encodes the rules of the calculus **EP** [6], as implemented in Leo-III.

- **`MetaTheorems.lp`**  
  Contains theorems allowing operations on literals of a given clause:
  - Deletion of ⊥ at a given index in a clause.
  - An n-ary version of the standard library theorem `transform` (from `Disj.lp`).

- **`UserTactic.lp`**  
  Defines user-defined tactics applied in the verification of Leo-III proofs. This includes:
  - Exhaustive application of Boolean identities to verify term simplification inferences.
  - Exhaustive application of Boolean identities to verify clausification steps.
  - Automated replacement of trivially false literals (e.g. ¬⊤) with ⊥ to simplify subsequent removal from clauses.
  - Normalization of equational literals with ⊤ or ⊥ on the left- or right-hand side.

## Dependencies

Some of the encodings rely on features added after the latest stable releases of Lambdapi and the Lambdapi standard library. You must install the latest development versions of both. Please follow the instructions in the respective repositories for:
- [Lambdapi](https://github.com/Deducteam/lambdapi)
- [Lambdapi Standard Library](https://github.com/Deducteam/lambdapi-stdlib)

## Installation from Source

Assuming Lambdapi is already installed, you can install this package by running:
```
make install
```

## Usage

To use these encodings in your Lambdapi files, simply require them as follows:
```
require open Leo-III-lambdapi-lib.EPrules Leo-III-lambdapi-lib.MetaTheorems Leo-III-lambdapi-lib.SimpTactic;
```


## References and Related Projects
1. [Leo-III: A Higher-Order Logic Automated Theorem Prover](https://github.com/leoprover/Leo-III)  
2. [Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory](https://inria.hal.science/hal-04281492/document)  
3. [Lambdapi: An Interactive Proof Assistant for Dedukti](https://github.com/Deducteam/lambdapi)
4. [Lambdapi-producing version of Leo-III](https://github.com/melanie-taprogge/Leo-III)
5. [Standard library of Lambdapi](https://github.com/Deducteam/lambdapi-stdlib/tree/master)
6. [Extensional Higher-Order Paramodulation in Leo-III](https://arxiv.org/pdf/1907.11501)

