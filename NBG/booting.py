import os
import sys
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

# pylint: disable=unused-wildcard-import
from node import *
from variables import *

# start!

# logic
def logic(target, *sources):
    return target.logic(*sources)

remember(logic)

true = Node("logical", "true", []).by()
false = Node("logical", "false", [])

pre_unary("not", "not")
binary("and", "and")
binary("or", "or")
binary("imply", "imply")
binary("iff", "iff")

# definition of set
clean()
from variables import *

binary("in", "in")

def Set(x):
    return Node("property", "set", [x])

from variables import *
Exist(C, x @ C).define_property("set").export("definition_of_set")

def is_set(target, reason): # x in C => Set(x)
    x = reason.left()
    definition_of_set = theorems["definition_of_set"]
    C0 = definition_of_set.get_exist_variables()[0]
    xs = Set(x).logic(Exist(C0, x @ C0).found(reason), definition_of_set.put(x))
    return xs

remember(is_set)


# axiom of extensionality
clean()
from variables import *

All(A, All(B, All(x, Set(x) >> ((x @ A) == (x @ B))) >> (A == B))).axiom().export("axiom_of_extensionality")

def uniqueness_from_extensionality(target):
    # target : Unique(A, bound & All(x, Set(x) >> ((x @ A) == condition)))
    A = target.variable()
    statement = target.statement()
    bound = None
    if statement.is_logical() and statement.name() == "and": # bounded case
        bound = statement.left()
        statement = statement.right()
    B = Variable("UFE_1")
    C = Variable("UFE_2")

    extensionality = theorems["axiom_of_extensionality"].put(B).put(C)
    x0 = extensionality.get_all_variables()[0]

    target_B = statement.substitute(A, B)
    target_C = statement.substitute(A, C)
    if bound:
        with bound.substitute(A, B) & target_B as bounded_target_B:
            with bound.substitute(A, C) & target_C as bounded_target_C:
                target_B.logic(bounded_target_B)
                target_C.logic(bounded_target_C)
                with Set(x0) as x0s:
                    ((x0 @ B) == (x0 @ C)).logic(x0s, target_B.put(x0), target_C.put(x0))
                xB_xC = escape()
                all_xs_xB_xC = xB_xC.gen(x0)
                (B == C).by(all_xs_xB_xC, extensionality)
        
        result = escape()
        result = ((result.left() & result.right().left()) >> (B == C)).by(escape()).gen(C).gen(B)
        
        return result.assert_unique(A)
    else:
        with target_B as bounded_target_B:
            with target_C as bounded_target_C:
                target_B.logic(bounded_target_B)
                target_C.logic(bounded_target_C)
                with Set(x0) as x0s:
                    ((x0 @ B) == (x0 @ C)).logic(x0s, target_B.put(x0), target_C.put(x0))
                xB_xC = escape()
                all_xs_xB_xC = xB_xC.gen(x0)
                (B == C).by(all_xs_xB_xC, extensionality)
        
        result = escape()
        result = ((result.left() & result.right().left()) >> (B == C)).by(escape()).gen(C).gen(B)
        
        return result.assert_unique(A)

remember(uniqueness_from_extensionality)


# axiom of pairing
clean()
from variables import *

axiom_of_pairing = All(x, Set(x) >> All(y, Set(y) >> Exist(p, Set(p) & All(z, Set(z) >> ((z @ p) == ((z == x) | (z == y)))))))
axiom_of_pairing.axiom().export("axiom_of_pairing")
with Set(x) as xs:
    with Set(y) as ys:
        exist_p = axiom_of_pairing.bounded_put(x, xs).bounded_put(y, ys)
        unique_p = Unique(p, Set(p) & All(z, Set(z) >> ((z @ p) == ((z == x) | (z == y)))))
        unique_p = unique_p.by()
        (unique_p & exist_p).logic(unique_p, exist_p)
    escape().gen(y)
uniquely_exist = escape().gen(x)

uniquely_exist.define_function("pairing").export("definition_of_pairing")

def Pairing(a, b):
    return Node("function", "pairing", [a, b])

binary("pairing", "#")

def pairing_is_set(target, as_, bs):
    a = as_.body()
    b = bs.body()
    definition_of_pairing = theorems["definition_of_pairing"].bounded_put(a, as_).bounded_put(b, bs)
    abs_ = Set(Pairing(a, b)).by(definition_of_pairing)
    return abs_

remember(pairing_is_set)

def property_of_pairing(target, x_in_a_pair_b, as_, bs):
    x = x_in_a_pair_b.left()
    a = x_in_a_pair_b.right().left()
    b = x_in_a_pair_b.right().right()
    xs = Set(x).by(x_in_a_pair_b)
    definition_of_pairing = theorems["definition_of_pairing"].bounded_put(a, as_).bounded_put(b, bs)
    P = definition_of_pairing.right().by(definition_of_pairing).bounded_put(x, xs)
    P = P.right().by(P, x_in_a_pair_b)
    return P

remember(property_of_pairing)


# membership_class
clean()
from variables import *

axiom_of_membership = Exist(E, All(x, Set(x) >> All(y, Set(y) >> ((Pairing(x, y) @ E) == (x @ y)))))
axiom_of_membership.axiom().export("axiom_of_membership")

definition_of_membership_class = axiom_of_membership.let("membership_class")

def Membership_class():
    return Node("variable", "membership_class", [])

# intersection_function
clean()
from variables import *

axiom_of_intersection = All(A, All(B, Exist(C, All(x, Set(x) >> ((x @ C) == ((x @ A) & (x @ B)))))))
axiom_of_intersection.axiom().export("axiom_of_intersection")

uniqueness_of_intersection = Unique(C, All(x, Set(x) >> ((x @ C) == ((x @ A) & (x @ B)))))
uniqueness_of_intersection = uniqueness_of_intersection.by()
uniquely_exist = (uniqueness_of_intersection & axiom_of_intersection.put(A).put(B)).by(uniqueness_of_intersection, axiom_of_intersection.put(A).put(B))
uniquely_exist = uniquely_exist.gen(B).gen(A)

definition_of_cap = uniquely_exist.define_function("cap")
definition_of_cap.export("definition_of_cap")

binary("cap", "cap")

def Cap(A, B):
    return Node("function", "cap", [A, B])

def property_of_cap_left(target, x_in_A_cap_B):
    x = x_in_A_cap_B.left()
    xs = Set(x).by(x_in_A_cap_B)
    A = x_in_A_cap_B.right().left()
    B = x_in_A_cap_B.right().right()
    definition_of_cap = theorems["definition_of_cap"].put(A).put(B).bounded_put(x, xs)
    return (x @ A).by(definition_of_cap, x_in_A_cap_B)

remember(property_of_cap_left)

def property_of_cap_right(target, x_in_A_cap_B):
    x = x_in_A_cap_B.left()
    xs = Set(x).by(x_in_A_cap_B)
    A = x_in_A_cap_B.right().left()
    B = x_in_A_cap_B.right().right()
    definition_of_cap = theorems["definition_of_cap"].put(A).put(B).bounded_put(x, xs)
    return (x @ B).by(definition_of_cap, x_in_A_cap_B)

remember(property_of_cap_right)


# complement_function
clean()
from variables import *

axiom_of_complement = All(A, Exist(B, All(x, Set(x) >> ((x @ B) == ~(x @ A)))))
axiom_of_complement.axiom().export("axiom_of_complement")

uniqueness_of_complement = Unique(B, All(x, Set(x) >> ((x @ B) == ~(x @ A))))
uniqueness_of_complement = uniqueness_of_complement.by()
uniquely_exist = (uniqueness_of_complement & axiom_of_complement.put(A)).by(uniqueness_of_complement, axiom_of_complement.put(A))
uniquely_exist = uniquely_exist.gen(A)

definition_of_complement = uniquely_exist.define_function("complement")
definition_of_complement.export("definition_of_complement")

def Complement(A):
    return Node("function", "complement", [A])

def property_of_complement(target, x_in_cA):
    x = x_in_cA.left()
    xs = Set(x).by(x_in_cA)
    A = x_in_cA.right().body()
    definition_of_complement = theorems["definition_of_complement"].put(A).bounded_put(x, xs)
    return (~(x @ A)).by(definition_of_complement, x_in_cA)

remember(property_of_complement)

# empty_class
clean()
from variables import *


empty_class = A & ~A
with x @ empty_class as xe:
    xA = property_of_cap_left(x @ A, xe)
    xA = (x @ A).by(xe)
    xcA = (x @ ~A).by(xe)
    nxA = (~(x @ A)).by(xcA)
    false.by(xA, nxA)
nxe = (~(x @ empty_class)).by(escape())
nxe = (Set(x) >> nxe).by(nxe).gen(x)
existence_of_empty_class = Exist(A, All(x, Set(x) >> ~(x @ A))).found(nxe)
uniqueness_of_empty_class = Unique(A, All(x, Set(x) >> ~(x @ A))).by()

uniquely_exist = (existence_of_empty_class & uniqueness_of_empty_class).by(existence_of_empty_class, uniqueness_of_empty_class)
definition_of_empty_class = uniquely_exist.define_function("empty_class").export("definition_of_empty_class")

def EmptyClass():
    return Node("function", "empty_class", [])


# ordered_pair
def OrderedPair(a, b):
    return Pairing(Pairing(a, a), Pairing(a, b))

