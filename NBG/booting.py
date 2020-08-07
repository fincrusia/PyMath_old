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


# equality
binary("equal", "==")

def use_of_equality(target, *reasons):
    return target.equal(*reasons)

remember(use_of_equality)

def reflection_of_equality(target, A_is_B):
    A = A_is_B.left()
    B = A_is_B.right()
    B_is_B = (B == B).by()
    B_is_A = (B == A).by(B_is_B, A_is_B)
    return B_is_A

remember(reflection_of_equality)

def reflection_of_non_equality(target, A_is_not_B):
    A_is_B = A_is_not_B.body()
    A = A_is_B.left()
    B = A_is_B.right()
    with B == A as B_is_A:
        A_is_B = (A == B).by(B_is_A)
        false.by(A_is_B, A_is_not_B)
    B_is_not_A = (B != A).by(escape())
    return B_is_not_A

remember(reflection_of_non_equality)

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
    xs = Set(x).by(Exist(C0, x @ C0).found(reason), definition_of_set.put(x))
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
                target_B.by(bounded_target_B)
                target_C.by(bounded_target_C)
                with Set(x0) as x0s:
                    ((x0 @ B) == (x0 @ C)).by(x0s, target_B.put(x0), target_C.put(x0))
                xB_xC = escape()
                all_xs_xB_xC = xB_xC.gen(x0)
                (B == C).by(all_xs_xB_xC, extensionality)
        
        result = escape()
        result = ((result.left() & result.right().left()) >> (B == C)).by(escape()).gen(C).gen(B)
        
        return result.assert_unique(A)
    else:
        with target_B as bounded_target_B:
            with target_C as bounded_target_C:
                target_B.by(bounded_target_B)
                target_C.by(bounded_target_C)
                with Set(x0) as x0s:
                    ((x0 @ B) == (x0 @ C)).by(x0s, target_B.put(x0), target_C.put(x0))
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
        exist_p = axiom_of_pairing.bput(x, xs).bput(y, ys)
        unique_p = Unique(p, Set(p) & All(z, Set(z) >> ((z @ p) == ((z == x) | (z == y)))))
        unique_p = unique_p.by()
        (unique_p & exist_p).by(unique_p, exist_p)
    escape().gen(y)
uniquely_exist = escape().gen(x)

uniquely_exist.define_function("pairing").export("definition_of_pairing")

def Pairing(a, b):
    return Node("function", "pairing", [a, b])

binary("pairing", "#")

def pairing_is_set(target, as_, bs):
    a = as_.body()
    b = bs.body()
    definition_of_pairing = theorems["definition_of_pairing"].bput(a, as_).bput(b, bs)
    abs_ = Set(Pairing(a, b)).by(definition_of_pairing)
    return abs_

remember(pairing_is_set)

def property_of_pairing_1(target, x_in_a_pair_b, as_, bs):
    x = x_in_a_pair_b.left()
    a = x_in_a_pair_b.right().left()
    b = x_in_a_pair_b.right().right()
    xs = Set(x).by(x_in_a_pair_b)
    definition_of_pairing = theorems["definition_of_pairing"].bput(a, as_).bput(b, bs)
    P = definition_of_pairing.right().by(definition_of_pairing).bput(x, xs)
    P = P.right().by(P, x_in_a_pair_b)
    return P

remember(property_of_pairing_1)

def property_of_pairing_2(target, as_, bs):
    a = as_.body()
    b = bs.body()
    definition_of_pairing = theorems["definition_of_pairing"].bput(a, as_).bput(b, bs)
    definition_of_pairing = definition_of_pairing.right().by(definition_of_pairing).bput(a, as_)
    result = (a @ Pairing(a, b)).by(definition_of_pairing, (a == a).by())
    return result

remember(property_of_pairing_2)

def property_of_pairing_3(target, as_, bs):
    a = as_.body()
    b = bs.body()
    definition_of_pairing = theorems["definition_of_pairing"].bput(a, as_).bput(b, bs)
    definition_of_pairing = definition_of_pairing.right().by(definition_of_pairing).bput(b, bs)
    result = (b @ Pairing(a, b)).by(definition_of_pairing, (b == b).by())
    return result

remember(property_of_pairing_3)

def property_of_pairing_4(target, x_in_uaa, as_):
    a = as_.body()
    x = x_in_uaa.left()
    xs = Set(x).by(x_in_uaa)
    definition_of_pairing = theorems["definition_of_pairing"].bput(a, as_).bput(a, as_)
    definition_of_pairing = definition_of_pairing.right().by(definition_of_pairing).bput(x, xs)
    x_is_a_or_a = ((x == a) | (x == a)).by(definition_of_pairing, x_in_uaa)
    x_is_a = (x == a).by(x_is_a_or_a)
    return x_is_a

remember(property_of_pairing_4)


def MembershipClass():
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
    definition_of_cap = theorems["definition_of_cap"].put(A).put(B).bput(x, xs)
    return (x @ A).by(definition_of_cap, x_in_A_cap_B)

remember(property_of_cap_left)

def property_of_cap_right(target, x_in_A_cap_B):
    x = x_in_A_cap_B.left()
    xs = Set(x).by(x_in_A_cap_B)
    A = x_in_A_cap_B.right().left()
    B = x_in_A_cap_B.right().right()
    definition_of_cap = theorems["definition_of_cap"].put(A).put(B).bput(x, xs)
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
    definition_of_complement = theorems["definition_of_complement"].put(A).bput(x, xs)
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
clean()
from variables import *

def OrderedPair(a, b):
    return Pairing(Pairing(a, a), Pairing(a, b))

def ordered_pair_is_set(target, as_, bs):
    a = as_.body()
    b = bs.body()
    uab = Pairing(a, b)
    uaa = Pairing(a, a)
    ab = OrderedPair(a, b)
    uabs = Set(uab).by(as_, bs)
    uaas = Set(uaa).by(as_, as_)
    abs_ = Set(ab).by(uaas, uabs)
    return abs_

remember(ordered_pair_is_set)

with Set(a) as as_:
    with Set(b) as bs:
        with Set(x) as xs:
            with Set(y) as ys:
                uab = Pairing(a, b)
                uxy = Pairing(x, y)
                uaa = Pairing(a, a)
                uaas = Set(uaa).by(as_, as_)
                uxx = Pairing(x, x)
                uxxs = Set(uxx).by(xs, xs)
                uabs = Set(uab).by(as_, bs)
                uxys = Set(uxy).by(xs, ys)
                ab = OrderedPair(a, b)
                xy = OrderedPair(x, y)
                abs_ = Set(ab).by(as_, bs)
                xys = Set(xy).by(xs, ys)
                with ab == xy as ab_xy:
                    a_in_uaa = (a @ uaa).by(as_, as_)
                    a_in_uab = (a @ uab).by(as_, bs)
                    with c @ ab as c_ab:
                        c_is_uaa_or_uab = ((c == uaa) | (c == uab)).by(c_ab, uaas, uabs)
                        with c == uaa as c_is_uaa:
                            a_in_c = (a @ c).by(a_in_uaa, c_is_uaa)
                        c_is_uaa_case = escape()
                        with c == uab as c_is_uab:
                            a_in_c = (a @ c).by(a_in_uab, c_is_uab)
                        c_is_uab_case = escape()
                        a_in_c = (a @ c).by(c_is_uaa_case, c_is_uab_case, c_is_uaa_or_uab)
                    a_in_uxx = escape().gen(c).put(uxx)
                    uxx_in_ab = (uxx @ ab).by((uxx @ xy).by(uxxs, uxys), ab_xy)
                    a_in_uxx = (a @ uxx).by(a_in_uxx, uxx_in_ab)
                    a_is_x = (a == x).by(a_in_uxx, xs)

                    uab_in_xy = (uab @ xy).by((uab @ ab).by(uaas, uabs), ab_xy)
                    uab_is_uxx_or_uxy = ((uab == uxx) | (uab == uxy)).by(uab_in_xy, uxxs, uxys)
                    b_in_uab = (b @ uab).by(as_, bs)
                    with x == y as x_is_y:
                        uxx_is_uxy = (uxx == uxy).by((uxx == uxx).by(), x_is_y)
                        uab_is_uxx_or_uxx = ((uab == uxx) | (uab == uxx)).by(uab_is_uxx_or_uxy, uxx_is_uxy)
                        uab_is_uxx = (uab == uxx).by(uab_is_uxx_or_uxx)
                        b_in_uxx = (b @ uxx).by(b_in_uab, uab_is_uxx)
                        b_is_x = (b == x).by(b_in_uxx, xs)
                        b_is_y = (b == y).by(b_is_x, x_is_y)
                        y_is_b = (y == b).by(b_is_y)
                    x_is_y_then_y_is_b = escape()

                    uxy_in_ab = (uxy @ ab).by((uxy @ xy).by(uxxs, uxys), ab_xy)
                    uxy_is_uaa_or_uab = ((uxy == uaa) | (uxy == uab)).by(uxy_in_ab, uaas, uabs)
                    y_in_uxy = (y @ uxy).by(xs, ys)
                    with a == b as a_is_b:
                        uaa_is_uab = (uaa == uab).by((uaa == uaa).by(), a_is_b)
                        uxy_is_uaa_or_uaa = ((uxy == uaa) | (uxy == uaa)).by(uxy_is_uaa_or_uab, uaa_is_uab)
                        uxy_is_uaa = (uxy == uaa).by(uxy_is_uaa_or_uaa)
                        y_in_uaa = (y @ uaa).by(y_in_uxy, uxy_is_uaa)
                        y_is_a = (y == a).by(y_in_uaa, as_)
                        y_is_b = (y == b).by(y_is_a, a_is_b)
                    a_is_b_then_y_is_b = escape()

                    with a != b as a_is_not_b:
                        with x != y as x_is_not_y:
                            a_is_not_y = (a != y).by(x_is_not_y, a_is_x)
                            with uxy == uaa as uxy_is_uaa:
                                y_in_uaa = (y @ uaa).by(y_in_uxy, uxy_is_uaa)
                                y_is_a = (y == a).by(y_in_uaa, as_)
                                a_is_y = (a == y).by(y_is_a)
                                false.by(a_is_y, a_is_not_y)
                            uxy_is_not_uaa = (uxy != uaa).by(escape())
                            uxy_is_uab = (uxy == uab).by(uxy_is_uaa_or_uab, uxy_is_not_uaa)
                            y_in_uab = (y @ uab).by(y_in_uxy, uxy_is_uab)
                            y_is_a_or_b = ((y == a) | (y == b)).by(y_in_uab, as_, bs)
                            y_is_not_a = (y != a).by(a_is_not_y)
                            y_is_b = (y == b).by(y_is_a_or_b, y_is_not_a)
                    a_is_not_b_and_x_is_not_y_then_y_is_b = escape()

                    y_is_b = (y == b).by(a_is_b_then_y_is_b, x_is_y_then_y_is_b, a_is_not_b_and_x_is_not_y_then_y_is_b)
                    b_is_y = (b == y).by(y_is_b)
                    a_is_x_and_y_is_b = (a_is_x & b_is_y).by(a_is_x, b_is_y)
            escape(y)
        escape(x)
    escape(b)
escape(a).export("comparison_of_ordered_pair")


# definition of tuple
clean()
from variables import *

definition = composite_function("ordered_pair", Pairing(Pairing(a, a), Pairing(a, b)), a, b)
definition.export("definition_of_ordered_pair")

def OrderedPair2(a, b):
    return Node("function", "ordered_pair", [a, b])

binary("ordered_pair", ",")

def ordered_pair_is_set_2(target, as_, bs):
    a = as_.body()
    b = bs.body()
    ab0s = Set(OrderedPair(a, b)).by(as_, bs)
    definition = theorems["definition_of_ordered_pair"].put(a).put(b)
    abs_ = Set(OrderedPair2(a, b)).by(ab0s, definition)
    return abs_

remember(ordered_pair_is_set_2)

with Set(a) as as_:
    with Set(b) as bs:
        with Set(x) as xs:
            with Set(y) as ys:
                with OrderedPair2(a, b) == OrderedPair2(x, y) as ab_xy:
                    definition = theorems["definition_of_ordered_pair"]
                    ab_def = definition.put(a).put(b)
                    xy_def = definition.put(x).put(y)
                    ab0_xy = (OrderedPair(a, b) == OrderedPair2(x, y)).by(ab_xy, ab_def)
                    ab0_xy0 = (OrderedPair(a, b) == OrderedPair(x, y)).by(ab0_xy, xy_def)
                    comparison = theorems["comparison_of_ordered_pair"].bput(a, as_).bput(b, bs).bput(x, xs).bput(y, ys)
                    comparison = ((a == x) & (b == y)).by(comparison, ab0_xy0)
            escape(y)
        escape(x)
    escape(b)
escape(a).export("comparison_of_ordered_pair_2")

def Tuple(*arguments):
    if len(arguments) == 0:
        return empty_class
    elif len(arguments) == 1:
        return arguments[0]
    else:
        node = arguments[0]
        for argument in arguments[1:]:
            node = OrderedPair2(node, argument)
        return node

def tuple_comparison(target, A_is_B, *bounds):
    arity = len(bounds) // 2
    A_node = A_is_B.left()
    for _ in range(0, arity - 1):
        A_node = A_node.left()
    A_bounds = []
    A_bounds.append(Set(A_node).by(bounds[0]))
    for index in range(1, arity):
        A_bounds.append(Set(OrderedPair2(A_node, bounds[index].body())).by(bounds[index], A_bounds[index - 1]))
        A_node = OrderedPair2(A_node, bounds[index].body())
    B_node = A_is_B.right()
    for _ in range(0, arity - 1):
        B_node = B_node.left()
    B_bounds = []
    B_bounds.append(Set(B_node).by(bounds[arity]))
    for index in range(1, arity):
        B_bounds.append(Set(OrderedPair2(B_node, bounds[arity + index].body())).by(bounds[arity + index], B_bounds[index - 1]))
        B_node = OrderedPair2(B_node, bounds[arity + index].body())

    A_node = A_is_B.left()
    B_node = A_is_B.right()
    
    equality = A_is_B
    for index in reversed(range(1, arity)):
        theorem = theorems["comparison_of_ordered_pair_2"]
        theorem = theorem.bput(A_node.left(), A_bounds[index - 1]).bput(A_node.right(), bounds[index])
        theorem = theorem.bput(B_node.left(), B_bounds[index - 1]).bput(B_node.right(), bounds[arity + index])
        left_equality = (A_node.left() == B_node.left()).by(theorem, equality)
        right_equality = (A_node.right() == B_node.right()).by(theorem, equality)
        if target.compare(right_equality):
            return right_equality
        if index == 1:
            return left_equality
        equality = left_equality
        A_node = A_node.left()
        B_node = B_node.left()

remember(tuple_comparison)


# definition of membership class 2
clean()
from variables import *

Exist(E, All(x, Set(x) >> All(y, Set(y) >> ((Tuple(x, y) @ E) == (x @ y))))).axiom().export("axiom_of_membership")


# axiom of domain
clean()
from variables import *

All(A, Exist(B, All(x, Set(x) >> ((x @ B) == Exist(y, Set(y) & (Tuple(x, y) @ A)))))).axiom().export("axiom_of_domain")


# product by V
clean()
from variables import *

All(A, Exist(B, All(u, Set(u) >> ((u @ B) == Exist(x, Set(x) & (Exist(y, Set(y) & (u == Tuple(x, y))) & (x @ A))))))).axiom().export("product_by_V")


# circular permutation
clean()
from variables import *

All(A, Exist(B, All(x, Set(x) >> All(y, Set(y) >> All(z, Set(z) >> ((Tuple(z, x, y) @ B) == (Tuple(x, y, z) @ A))))))).axiom().export("circular_permutation")


# transposition
clean()
from variables import *

All(A, Exist(B, All(x, Set(x) >> All(y, Set(y) >> All(z, Set(z) >> (((Tuple(x, z, y) @ B) == (Tuple(x, y, z) @ A)))))))).axiom().export("axiom_of_transposition")


# tuple lemma
clean()
from variables import *

B0 = B
with Set(x) as xs:
    with Set(y) as ys:
        with Set(z) as zs:
            xy = Tuple(x, y)
            xys = Set(xy).by(xs, ys)
            xyz = Tuple(x, y, z)
            xyzs = Set(xyz).by(xys, zs)
            AV = theorems["product_by_V"].put(A).let("TL_0")
            B = Variable("TL_0")
            x0, y0 = AV.get_exist_variables()
            xy_AV = AV.bput(xyz, xyzs)

            with xy @ A as xy_A:
                xyz_xyz = (xyz == xyz).by()
                xyz_xyz = (ys & xyz_xyz).by(xyz_xyz, ys)
                xyz_xyy0 = Exist(y0, Set(y0) & (xyz == Tuple(xy, y0))).found(xyz_xyz)
                xyz_xyy0 = (xyz_xyy0 & xy_A).by(xyz_xyy0, xy_A)
                xyz_xyy0 = (xys & xyz_xyy0).by(xys, xyz_xyy0)
                xyz_x0y0 = Exist(x0, Set(x0) & (Exist(y0, Set(y0) & (xyz == Tuple(x0, y0))) & (x0 @ A))).found(xyz_xyy0)
                xyz_B = (xyz @ B).by(xyz_x0y0, xy_AV)
            xy_A_imply_xyz_B = escape()

            with xyz @ B as xyz_B:
                x0_def = xyz_x0y0 = xy_AV.right().by(xyz_B, xy_AV).let("TL_1")
                x0 = Variable("TL_1")
                x0s = x0_def.left().by(x0_def)
                x0_def = x0_def.right().by(x0_def)
                x0_A = x0_def.right().by(x0_def)
                x0_def = x0_def.left()
                y0_def = x0_def.let("TL_2")
                y0s = y0_def.left().by(y0_def)
                y0_def = y0_def.right().by(y0_def)
                y0 = Variable("TL_2")
                xy_x0 = (xy == x0).by(y0_def, xys, zs, x0s, y0s)
                xy_A = (xy @ A).by(xy_x0, x0_A)
            xyz_B_imply_xy_A = escape()
            xyz_B_iff_xy_A = (xyz_B_imply_xy_A.left() == xyz_B_imply_xy_A.right()).by(xyz_B_imply_xy_A, xy_A_imply_xyz_B)
        escape(z)
    escape(y)
result = escape(x)
result = Exist(B0, result.substitute(B, B0)).found(result)

clean()
from variables import *

B0 = B
with Set(x) as xs:
    with Set(y) as ys:
        with Set(z) as zs:
            xy = Tuple(x, y)
            xys = Set(xy).by(xs, ys)
            xyz = Tuple(x, y, z)
            xyzs = Set(xyz).by(xys, zs)
            AB = theorems["tuple_lemma_3"].put(A).let("TL_3")
            AB = AB.bput(x, xs).bput(y, ys).bput(z, zs)
            B = Variable("TL_3")
            BC = theorems["axiom_of_transposition"].put(B).let("TL_4")
            BC = BC.bput(x, xs).bput(y, ys).bput(z, zs)
            C = Variable("TL_4")
            xzy = Tuple(x, z, y)
            with xy @ A as xy_A:
                xyz_B = (xyz @ B).by(xy_A, AB)
                xzy_C = (xzy @ C).by(xyz_B, BC)
            xy_A_imply_xzy_C = escape()
            with xzy @ C as xzy_C:
                xyz_B = (xyz @ B).by(xzy_C, BC)
                xy_A = (xy @ A).by(AB, xyz_B)
            xzy_C_imply_xy_A = escape()
            xzy_C_iff_xy_A = (xzy_C_imply_xy_A.left() == xy_A_imply_xzy_C.left()).by(xy_A_imply_xzy_C, xzy_C_imply_xy_A)
        escape(z)
    escape(y)
result = escape(x)
Exist(B0, result.substitute(C, B0)).found(result).gen(A).export("tuple_lemma_2")


clean()
from variables import *

B0 = B
with Set(x) as xs:
    with Set(y) as ys:
        with Set(z) as zs:
            xy = Tuple(x, y)
            xys = Set(xy).by(xs, ys)
            xyz = Tuple(x, y, z)
            xyzs = Set(xyz).by(xys, zs)
            AB = theorems["tuple_lemma_3"].put(A).let("TL_5").bput(x, xs).bput(y, ys).bput(z, zs)
            B = Variable("TL_5")
            BC = theorems["circular_permutation"].put(B).let("TL_6").bput(x, xs).bput(y, ys).bput(z, zs)
            C = Variable("TL_6")
            zxy = Tuple(z, x, y)
            zxy_C_iff_xy_A = ((zxy @ C) == (xy @ A)).by(BC, AB)
        escape(z)
    escape(y)
result = escape(x)
Exist(B0, result.substitute(Variable("TL_6"), B0)).found(result).gen(A).export("tuple_lemma_1")


clean()
from variables import *

B0 = B
with Set(x) as xs:
    with Set(y) as ys:
        with Set(z) as zs:
            xy = Tuple(x, y)
            xys = Set(xy).by(xs, ys)
            xyz = Tuple(x, y, z)
            xyzs = Set(xyz).by(xys, zs)
            AB = theorems["tuple_lemma_2"].put(A).let("TL_7").bput(x, xs).bput(y, ys).bput(z, zs)
            B = Variable("TL_7")
            BC = theorems["circular_permutation"].put(B).let("TL_8").bput(x, xs).bput(z, zs).bput(y, ys)
            C = Variable("TL_8")
            yxz = Tuple(y, x, z)
            yxz_C_iff_xy_A = ((yxz @ C) == (xy @ A)).by(AB, BC)
        yxz_C_iff_xy_A = escape(z)

        yx = Tuple(y, x)
        yxs = Set(yx).by(xs, ys)

        axiom_of_domain = theorems["axiom_of_domain"].put(C).let("TL_9")
        D = Variable("TL_9")

        xy_D_iff = axiom_of_domain.bput(yx, yxs)
        y0 = xy_D_iff.get_exist_variables()[0]

        with yx @ D as yx_D:
            existence = xy_D_iff.right().by(xy_D_iff, yx_D).let("TL_10")
            z0 = Variable("TL_10")
            z0s = Set(z0).by(existence)
            existence = existence.right().by(existence)
            lemma = yxz_C_iff_xy_A.bput(z0, z0s)
            xy_A = (xy @ A).by(lemma, existence)
        yx_D_imply_xy_A = escape()

        with xy @ A as xy_A:
            lemma = yxz_C_iff_xy_A.bput(x, xs)
            lemma = lemma.left().by(lemma, xy_A)
            lemma = (xs & lemma).by(xs, lemma)
            existence = Exist(y0, Set(y0) & (Tuple(y, x, y0) @ C)).found(lemma)
            yx_D = (yx @ D).by(xy_D_iff, existence)
        xy_A_imply_yx_D = escape()

        yx_D_iff_xy_A = ((yx @ D) == (xy @ A)).by(yx_D_imply_xy_A, xy_A_imply_yx_D)
    escape(y)
result = escape(x)
Exist(B0, result.substitute(Variable("TL_9"), B0)).found(result).gen(A).export("tuple_lemma_4")
