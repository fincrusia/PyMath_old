
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
There are three ways to generate node.

1. Using constructor of **Node**

This is not a pretty way, but you have to do this when you *define* high-level constructors.

2. Using defined constructors

For example, the following code generates a variable named *"x"*:

    x = Variable("x")

3. Using overloaded operators

**Recommanded**. The following code generates a sentence *"P implies Q"*:

    S = (P >> Q)




## Fitch-style Proof

To assume a sentence (P >> Q), and shorten it as A, write:

    with (P >> Q) as A:
        ... # some proof to deduce B
        B
    result = Node.last.copy() # this gives (A >> B), proved

A static member *"Node.last"* always points the lastly proved sentence.

Then the method *"copy()"* implements deep copy of the sentence.

Of course, you can use nested assumptions:

    with ... as A:
        with ... as B:
            ...
        result = Node.last.copy()
    result = Node.last.copy()



## Propositional deductions

When you got sentences *A*, *B*, *C*, which tautologically deduce *D*, just type:

    D = D.logic(A, B, C)

Then D is proved.


## Deductions with Quantifiers






## Some Rules

#### Method "prove_CAUTION()" is only for the implementation. **DO NOT** use in your proof.

#### Each top-level folder is dedicated for one axiomatic system, and the folders **MUST NOT** import each other.

For instance, a result of the ZF theory should not referred in the ZFC theory. Why? Even ZFC is stronger than ZF, properties and functions in ZF are not guaranteed to have same definitions with their counterparts in ZFC. Probabily the formers are longer, since ZF has fewer tools to define shortly. Hence, ZF and ZFC theories are not "synced" in general.

#### To avoid shallow copy of objects, use copy() method.

#### (Recommended) Rather than doing same things, use meta-theorems!

Making easy-to-use Python methods will contribute to the overall theory. Coding Generic functions might not be easy, but hope we choose the better way for the future.