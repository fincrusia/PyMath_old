
PyMath
=======================

# Purpose

To build mathematical theories on Python.

Purpose on easy proof-writing and automatic verification.

# Basic Concepts

## Nodes and Branches

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

You can overload operators in many ways using member of *attributes* of the *Node* class.


## Fitch-style Proof

To assume a sentence (P >> Q), and shorten it as A, write:

    with (P >> Q) as A:
        ... # some proof to deduce B
        B # proved

    result = Node.last.copy() # this gives (A >> B), proved

A static member *"Node.last"* always points the lastly proved sentence.

Then the method *"copy()"* implements deep copy of the sentence.

Of course, you can use nested assumptions:

    with ... as A:
        with ... as B:
            ...
        result = Node.last.copy()
    result = Node.last.copy()



## Propositional Deductions

When you got sentences *A*, *B*, *C*, which tautologically deduce *D*, just type:

    D = D.logic(A, B, C)

Then D is proved.


## Deductions with Quantifiers

To substitute an "all"-variable by a term, use *"put()"* method.

Conversely, *"gen()"* method generalizes a sentence with given "all"-variable.

If a term satisfies a property so you want to assert the existence of such object, use *"found()"* method.

You can use *"let()"* method to define a function(or a constant) from the existence sentence.

Similarly, *"say()"* method defines a property from any sentence.



## Auto-Deduction

One of the key-features of PyMath is the auto-deduction.

Basically it is not a sort of AI, proving something you didn't prove.

But since we are working on the Python, you can freely add functions generating proofs.

These "meta-theorems" can be added to *"Node.memory"*.

When you call the *"by()"* method, PyMath brutally applies all the meta-theorems to the given reasons.

    def meta_theorem(target, reason_1, reason_2, ...):
        ...
        # generate proof
        # do not need to worry for exceptions, since this function will called in the try-except sense.

    remember("name_of_the_theorem", meta_theorem)  # "cache" the function

    target.by(reason_1, reason_2, ...)  # this would prove the target


Of course, you can also use *"by()"* method inside meta-theorems.



## Exportations

You can export theorems so that they can be used in the other files:

    A.export("name_of_the_theorem")

    ...

    Node.theorems["name_of_the_theorem"]  # returns the theorem



## Option: Verbose

If you want to see all the sentence proved, use the method *"verbose()"*:

    ...  # mute

    verbose(True)
    
    ...  # prints out everything
    
    verbose (False)
    
    ...  # mute






## Some Rules

#### Method "prove_CAUTION()" is only for the implementation. **DO NOT** use in your proof.

#### Each top-level folder is dedicated for one axiomatic system, and the folders **MUST NOT** import each other.

For instance, a result of the ZF theory should not referred in the ZFC theory. Why? Even ZFC is stronger than ZF, properties and functions in ZF are not guaranteed to have same definitions with their counterparts in ZFC. Probabily the formers are longer, since ZF has fewer tools to define shortly. Hence, ZF and ZFC theories are not "synced" in general.

#### To avoid shallow copy of objects, use copy() method.

#### (Recommended) Rather than doing same things, use meta-theorems!

Making easy-to-use Python methods will contribute to the overall theory. Coding Generic functions might not be easy, but hope we choose the better way for the future.