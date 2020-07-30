
PyMath
=======================

## Purpose

To build mathematical theorys on Python.

Purpose on easy proof-writing and automatic verification.

## Basic Concepts

# Node and Branches

In **PyMath**, everything including sentences and terms are implemented as trees, using class **Node**.

It has a member **"branch"**, which is simply a list of non-negative integers.

When you assume something, an integer is appended at the end of the branch, so that the branch be longer.

If you deduce a sentence *P*, a sentence *"assumption implies P"* has a branch of the original length.

When you prove something, you can only use sentences with same or shorter branches, with compatible elements.


# Fitch-style Proof





# Logical Tautologies

When you got sentences *A*, *B*, *C*, which tautologically deduce *D*, just type:

    D = D.logic(A, B, C)

Then D is proved.
