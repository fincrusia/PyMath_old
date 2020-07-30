
PyMath
=======================

# Purpose

To build mathematical theorys on Python.

Purpose on easy proof-writing and automatic verification.

# Basic Concepts

## Node and Branches

In **PyMath**, everything including sentences and terms are implemented as trees, using class **Node**.

It has a member **"branch"**, which is simply a list of non-negative integers.

When you assume something, an integer is appended at the end of the branch, so that the branch be longer.

If you deduce a sentence *P*, a sentence *"assumption implies P"* has a branch of the original length.

When you prove something, you can only use sentences with same or shorter branches, with compatible elements.


## Generating Nodes




## Fitch-style Proof





## Logical Tautologies

When you got sentences *A*, *B*, *C*, which tautologically deduce *D*, just type:

    D = D.logic(A, B, C)

Then D is proved.



## Some Rules

#### Method "prove_CAUTION()" is only for the implementation. **DO NOT** use in your proof.

#### Each top-level folder is dedicated for one axiomatic system, and the folders **MUST NOT** import each other.

For instance, a result of the ZF theory should not referred in the ZFC theory. Why? Even ZFC is stronger than ZF, properties and functions in ZF are not guaranteed to have same definitions with their counterparts in ZFC. Probabily the formers are longer, since ZF has fewer tools to define shortly. Hence, ZF and ZFC theories are not "synced" in general.

#### (Recommended) Rather than doing same things, use meta-theorems!

Making easy-to-use Python methods will contribute to the overall theory. Coding Generic functions might not be easy, but hope we choose the better way for the future.