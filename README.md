
PyMath
=======================

# Purpose

To build the mathematical theories on Python.

Purpose on easy proof-writing and automatic verification.


# Basic Concepts

## Nodes and Branches

In **PyMath**, everything including sentences and terms are implemented as trees, using class **Node**.

It has a member **branch**, which is simply a list of non-negative integers.

When you assume something, an integer is appended at the end of the branch, so that the branch be longer.
If you deduce a sentence *P*, a sentence *assumption implies P* has a branch of the original length.

When you prove something, you can only use sentences with same or shorter branches then current branch, with compatible elements.


## Generating Nodes
There are three ways to generate node.

1. Using constructor of **Node**

This is not a pretty way, but you have to do this when you *define* high-level constructors.

2. Using defined constructors

For example, the following code generates a variable named *"x"*:

    x = Variable("x")

To use new variables, type:

    clean()
    from variables import *


3. Using overloaded operators

**Recommanded**. The following code generates a sentence *P implies Q*:

    S = (P >> Q)

Like the above example, many operators are overloaded to easily generate nodes.


## Fitch-style Proof

To assume a sentence (P >> Q), and shorten it as A, write:

    with (P >> Q) as A:
        ... # some proof to deduce B
        B.by(...) # now B is proved

    result = escape() # this gives (A >> B), proved

Of course, you can use nested assumptions:

    with ... as A:
        with ... as B:
            ...
            P.by(...) # P is proved
    result = escape() # (A >> (B >> P))



## Propositional Deductions

When you got sentences *A*, *B*, *C*, which tautologically deduce *D*, just type:

    D = D.logic(A, B, C)

Then D is proved.


## Deductions with Quantifiers

1st-order logic uses quantifiers, such as *all* and *exist*.

Unfortunately, there is no effective way to determine logically valid sentences.

So you have to prove by steps, using the following APIs:


1. *put()* : substitute a quantifier *all* by an instance.

    All(x, x @ A).put(y)   # y @ A

2. *assert_unique()* : from a proper sentence, drive uniqueness.

    uniqueness = All(x, All(y, (P(x) & P(y) >> (x == y)))).assert_unique(z)   # Unique(z, P(z))

3. *expand_unique()* : reverse *assert_unique*.

    a_is_b = Unique(c, Q(c)).expand_unique(a, b)   # a == b

4. *found()* : from an instance, assert existence.

    Exist(x, R(x)).found(R(a))   # Exist(x, R(x))

5. *gen()* : generalization

    S(x).gen(y)   # All(y, S(y))


## Defining New Properties and Functions

You can easily define new properties and functions using APIs.

    definition_of_new_function = All(x, Unique(y, P(x, y)) & Exist(y, P(x, y)).define_function("new_function")
    deinition_of_new_property = (any_sentence)



## Auto-Deduction

One of the key-features of PyMath is auto-deduction.

Basically it is not a sort of AI, proving something you didn't prove.

But since we are working on the Python, you can freely add functions generating proofs.

These "meta-theorems" can be added to *Node.memory*.

When you call the *by()* method, PyMath brutally applies all the meta-theorems to the given reasons.

    def meta_theorem(target, reason_1, reason_2, ...):
        ...
        # generate proof
        # do not need to worry for exceptions, since this function will called in the try-except sense.

    remember(meta_theorem)  # "remember" the meta-theorem

    target.by(reason_1, reason_2, ...)  # this might prove the target!


Of course, you can also use *by()* method inside meta-theorems.

However, to avoid infinite-loop, when a meta-theorem calls *by()*, it is not called inside the new *by()*


## Exportations

You can export theorems so that they can be used in the other files:

    A.export("name_of_the_theorem")

    ...

    theorems["name_of_the_theorem"]  # returns the theorem






## Some Rules

#### Method "axiom()" is only for the axioms. **DO NOT** use it in your proof.

#### Each top-level folder is dedicated for one axiomatic system, and the folders **MUST NOT** import each other.

For instance, a result of the ZF theory should not referred in the ZFC theory. Why? Even ZFC is stronger than ZF, properties and functions in ZF are not guaranteed to have same definitions with their counterparts in ZFC. Probabily the formers are longer, since ZF has fewer tools to define shortly. Hence, ZF and ZFC theories are not "synced" in general.

#### Node is immutable. **DO NOT** change.

#### (Recommended) Rather than doing same things, use meta-theorems!

Making easy-to-use Python methods will contribute to the overall theory. Coding Generic functions might not be easy, but hope we choose the better way for the future.