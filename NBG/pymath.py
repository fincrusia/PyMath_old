import os
import sys
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

class Node:
    cursor = -1
    branch = []
    assumptions = []
    non_generalizables = []
    last = None

    connections = ["and", "or", "not", "imply", "iff", "true", "false"]
    quantifiers = ["all", "exist"]

    verbose = False
    memory = {}
    names = set()
    theorems = {}

    # initialization
    def __init__(self, type_, name, children, attributes):
        if type_ == "logical":
            assert name in Node.connections
        elif type_ == "quantifier":
            assert name in Node.quantifiers
        else:
            assert (not name in Node.connections) and (not name in Node.quantifiers)
        self.type = type_
        self.name = name
        self.children = children
        self.attributes = attributes
        self.branch = None
        Node.names.add(name)

    def copy(self):
        children = [child.copy() for child in self.children]
        node = Node(self.type, self.name, children, self.attributes)
        if self.branch != None:
            node.branch = [x for x in self.branch]
        else:
            node.branch = None
        return node

    def set_(self, key, data):
        self.attributes[key] = data

    def unset(self, key):
        del self.attributes[key]
    
    def compare(self, A):
        if self.type != A.type or self.name != A.name or len(self.children) != len(A.children):
            return False
        for cursor in range(0, len(A.children)):
            if not self[cursor].compare(A[cursor]):
                return False
        return True

    def equal(self, A, *reason):
        if reason:
            reason = reason[0]
            assert reason.is_property and len(reason.children) == 2
        else:
            assert self.compare(A)
            return True
        a = reason.children[0]
        b = reason.children[1]
        if self.compare(A):
            return True
        elif self.compare(a) and A.compare(b):
            return True
        elif self.compare(b) and A.compare(a):
            return True
        else:
            if self.type != A.type or self.name != A.name or len(self.children) != len(A.children):
                return False
            for cursor in range(0, len(A.children)):
                if not self[cursor].equal(A[cursor]):
                    return False
            return True

    def __str__(self):
        if self.is_logical():
            if self.name in ["and", "or", "imply", "iff"]:
                return ("(" + str(self[0]) + " " + self.name + " " + str(self[1]) + ")")
            elif self.name in ["not"]:
                return ("(" + self.name + " " + str(self[0]) + ")")
            elif self.name in ["true", "false"]:
                return self.name
            else:
                assert False
        elif self.is_quantifier():
            return (self.name + "(" + str(self[0]) + "," + str(self[1]) + "," + str(self[2]) + ")")
        elif self.is_property() or self.is_function():
            if self["unary"]:
                assert len(self.children) == 1
                return ("(" + self["unary"] + " " + str(self[0]) + ")")
            elif self["binary"]:
                assert len(self.children) == 2
                return ("(" + str(self[0]) + " " + self["binary"] + " " + str(self[1]) + ")")
            elif len(self.children) == 0:
                return self.name
            else:
                result = (self.name + "(")
                for index, child in enumerate(self.children):
                    result += str(child)
                    if index != len(self.children) - 1:
                        result += ","
                result += ")"
                return result
        elif self.is_variable():
            return self.name[:-5]
        else:
            assert False

    def _repr(self, IDs):
        if self.is_variable():
            if not IDs.get(self.name):
                IDs[self.name] = len(IDs) + 1
            return ("#" + str(IDs[self.name]))
        else:
            result = (self.name + "(")
            for child in self.children:
                result += (repr(child) + ",")
            result += ")"
            return result

    def __repr__(self):
        return self._repr({})


    # assumptions
    def __enter__(self):
        Node.cursor += 1
        if(len(Node.branch) <= Node.cursor):
            Node.branch.append(0)
            Node.assumptions.append(self.copy())
            Node.non_generalizables.append(self.get_free_names())
        else:
            Node.branch[Node.cursor] += 1
            Node.assumptions[Node.cursor] = self.copy()
            Node.non_generalizables[Node.cursor] = self.get_free_names()
        node = self.copy()
        node.prove_CAUTION()
        return node

    def __exit__(self, *arguments):
        Node.last = (Node.assumptions[Node.cursor].copy() >> Node.last.copy())
        Node.cursor -= 1
        Node.last.prove_CAUTION()

    
    # operators
    def __or__(self, A):
        if self.is_sentence():
            return Node("logical", "or", [self.copy(), A.copy()], {})
        elif self.is_term():
            return Node("function", "pairing", [self.copy(), A.copy()], {"binary" : "cup"})
        else:
            assert False

    def __and__(self, A):
        if self.is_sentence():
            return Node("logical", "and", [self.copy(), A.copy()], {})
        elif self.is_term():
            return Node("function", "intersection", [self.copy(), A.copy()], {"binary" : "cap"})
        else:
            assert False

    def __invert__(self):
        if self.is_sentence():
            return Node("logical", "not", [self.copy()], {})
        elif self.is_term():
            return Node("function", "complement", [self.copy()], {})
        else:
            assert False

    def __rshift__(self, A):
        return Node("logical", "imply", [self.copy(), A.copy()], {})

    def __floordiv__(self, A):
        return Node("logical", "iff", [self.copy(), A.copy()], {})

    def __eq__(self, A):
        return Node("property", "equal", [self.copy(), A.copy()], {"binary" : "=="})
    
    def __lshift__(self, A):
        return Node("property", "inclusion", [self.copy(), A.copy()], {})

    def __matmul__(self, A):
        return Node("property", "in", [self.copy(), A.copy()], {"binary" : "in"})

    def __call__(self, *arguments):
        for argument in arguments:
            assert argument.is_term()
        if self.is_function() or self.is_property:
            children = [argument.copy() for argument in arguments]
            return Node(self.type, self.name, children, self.attributes)
        elif self.is_variable():
            children = [self.copy()]
            for argument in arguments:
                children.append(argument.copy())
            return Node("function", "evaluation", children, self.attributes)
        else:
            assert False

    def __getitem__(self, key):
        if isinstance(key, int):
           return self.children[key]
        elif isinstance(key, str):
            return self.attributes.get(key)
        else:
            assert False


    # querys
    def is_proved(self):
        if len(self.branch) > Node.cursor + 1:
            return False

        for cursor in range(0, len(self.branch)):
            if self.branch[cursor] != Node.branch[cursor]:
                return False
        return True

    def is_generalizable(self):
        assert self.is_variable()
        for cursor in range(0, Node.cursor + 1):
            if self.name in Node.non_generalizables[cursor]:
                return False
        return True

    def is_variable(self):
        return self.type == "variable"

    def is_property(self):
        return self.type == "property"

    def is_function(self):
        return self.type == "function"
    
    def is_quantifier(self):
        return self.type == "quantifier"

    def is_logical(self):
        return self.type == "logical"

    def is_term(self):
        if self.is_variable():
            return True
        elif self.is_function():
            for child in self.children:
                if not child.is_term():
                    return False
            return True
        else:
            return False

    def is_sentence(self):
        if self.is_property():
            return True
        elif self.is_logical():
            for child in self.children:
                if not child.is_sentence():
                    return False
            return True
        elif self.is_quantifier():
            return self[0].is_variable() and self[1].is_sentence() and self[2].is_sentence()
        else:
            return False

    def _is_readable(self, bounded):
        if self.type in Node.quantifiers and self.name in bounded:
            return False
        else:
            if self.type in Node.quantifiers:
                bounded |= set([self.name])
            for child in self.children:
                if not child._is_readable(bounded):
                    return False
            return True

    def is_readable(self):
        if not self.is_sentence():
            return False
        else:
            return self._is_readable(set())

    def is_closed(self):
        assert self.is_sentence()
        return not self.get_free_names()


    # APIs
    def _get_free_names(self, bounded):
        if self.is_variable() and not self.name in bounded:
            return set([self.name])
        
        if self.is_quantifier():
            bounded = (bounded | set([self[0].name]))

        free_names = set()
        for child in self.children:
            free_names |= child._get_free_names(bounded)
        
        return free_names

    def get_free_names(self):
        return self._get_free_names(set())

    def _substitute(self, variable, term):
        if self.is_variable and self.name == variable.name:
            return term.copy()
        elif self.is_quantifier() and self.children[0].name in term.get_free_names():
            assert False # for readability
        else:
            children = [child._substitute(variable, term) for child in self.children]
            return Node(self.type, self.name, children , self.attributes)

    def substitute(self, variable, term):
        assert variable.is_variable()
        assert term.is_term()
        return self._substitute(variable, term)

    def _contract(self, term, variable, free_names):
        if self.compare(term):
            return variable.copy()
        elif self.type in Node.quantifiers and self[0].name in free_names:
            assert False # for readability
        else:
            children = [child._contract(term, variable, free_names) for child in self.children]
            return Node(self.type, self.name, children, self.attributes)

    def contract(self, term, variable):
        assert term.is_term()
        assert variable.is_variable()
        free_names = term.get_free_names()
        return self._contract(term, variable, free_names)

    def logical_decomposition(self, atomics):
        if self.is_logical():
            children = []
            for child in self.children:
                child_decomposition, atomics = child.logical_decomposition(atomics)
                children.append(child_decomposition)
            return Node(self.type, self.name, children, {}), atomics
        else:
            for key, atomic in atomics.items():
                if self.compare(atomic):
                    return Node("atomic", key, [], {}), atomics
            atomics[len(atomics)] = self.copy()
            return Node("atomic", len(atomics) - 1, [], {}), atomics

    def logical_evaluation(self, truth):
        if self.type == "atomic":
            return truth[self.name]
        else:
            assert self.is_logical()
            if self.name == "and":
                return self[0].logical_evaluation(truth) and self[1].logical_evaluation(truth)
            elif self.name == "or":
                return self[0].logical_evaluation(truth) or self[1].logical_evaluation(truth)
            elif self.name == "not":
                return not self[0].logical_evaluation(truth)
            elif self.name == "imply":
                return (not self[0].logical_evaluation(truth)) or self[1].logical_evaluation(truth)
            elif self.name == "iff":
                return self[0].logical_evaluation(truth) == self[1].logical_evaluation(truth)
            elif self.name == "true":
                return True
            elif self.name == "false":
                return False
            else:
                assert False

    def get_exist_variable(self):
        result = []
        if self.is_quantifier and self.name == "exist":
            result.append(self[0].copy())
        for child in self.children:
            for exist_variable in child.get_exist_variable():
                result.append(exist_variable)
        return result


    # prove
    def prove_CAUTION(self):
        assert self.is_readable()
        self.branch = [x for x in Node.branch[ : Node.cursor + 1]]
        Node.last = self.copy()
        if Node.verbose:
            print(self)

    def export(self, name):
        assert self.is_proved()
        assert self.is_closed()
        Node.theorems[name] = self.copy()

    def put(self, term, bound):
        assert self.is_proved()
        assert bound.is_proved()
        assert self.is_quantifier() and self.name == "all"

        variable = self[0]
        bound_put = self[1].substitute(variable, term)
        sentence_put = self[2].substitute(variable, term)

        assert bound_put.compare(bound)

        sentence_put.prove_CAUTION()
        return sentence_put

    def _found(self, reason, term, variable):
        if self.compare(reason):
            return True
        elif self.compare(variable) and reason.compare(term):
            return True
        else:
            for index in range(0, len(self.children)):
                if not self[index]._found(reason[index], term, variable):
                    return False
            return True

    def found(self, reason, bound, term):
        assert self.is_quantifier() and self.name == "exist"
        assert reason.is_proved()
        assert term.is_term()
        assert bound.is_proved()
        variable = self[0].copy()
        assert self[1]._found(bound, term, variable)
        assert self[2]._found(reason, term, variable)
        self.prove_CAUTION()
        return self

    def let(self, name, **attributes):
        assert self.is_proved()
        assert not name in Node.names

        number_of_all = 0
        all_variables = []
        all_bounds = []
        cursor = self
        while cursor.is_quantifier() and cursor.name == "all":
            number_of_all += 1
            all_variables.append(cursor[0].copy())
            all_bounds.append(cursor[1].copy())
            cursor = cursor[2]
        assert cursor.is_quantifier() and cursor.name == "exist"

        exist_variable = cursor[0].copy()
        exist_bound = cursor[1].copy()
        exist_sentence = cursor[2].copy()

        new_function = Function(name, **attributes)

        exist_bound = exist_bound.substitute(exist_variable, new_function.copy()(*all_variables))
        exist_sentence = exist_sentence.substitute(exist_variable, new_function.copy()(*all_variables))

        for index in range(number_of_all - 1, -1, -1):
            exist_bound = _All(all_variables[index], all_bounds[index], exist_bound)
            exist_sentence = _All(all_variables[index], all_bounds[index], exist_sentence)

        exist_bound.prove_CAUTION()
        exist_sentence.prove_CAUTION()
        
        return new_function, exist_bound, exist_sentence

    def gen(self, variable, bound):
        assert self.is_proved()
        assert variable.is_generalizable()
        result = _All(variable, bound, self)
        result.prove_CAUTION()
        return result
    
    def say(self, name):
        assert self.is_sentence()
        assert not name in Node.names
        free_names = self.get_free_names()
        new_property = Property(name)
        free_variables = []
        for free_name in free_names:
            free_variables.append(Variable_namely(free_name))
        node = (new_property(*free_variables) // self.copy())
        for free_variable in reversed(free_variables):
            node = _All(free_variable, True_(), node)
        node.prove_CAUTION()
        return node, new_property.copy()

    def bound_to_assumption(self, source):
        assert self.is_sentence()
        assert source.is_proved()
        assert source.is_quantifier()
        x = source[0]
        bound = source[1]
        sentence = source[2]

        assert self.compare(Node("quantifier", source.name, [x, True_(), bound >> sentence], {}))
        self.prove_CAUTION()
        return self

    def assumption_to_bound(self, source):
        assert self.is_sentence()
        assert source.is_proved()
        assert source.is_quantifier()
        x = source[0]
        bound = source[1]
        assert source[2].is_logical() and source[2].name == "imply"
        assumption = source[2][0]
        sentence = source[2][1]

        new_bound = None
        if bound.compare(True_()):
            new_bound = assumption
        else:
            new_bound = bound & assumption
        assert self.compare(Node("quantifier", source.name, [x, new_bound, sentence], {}))
        self.prove_CAUTION()
        return self

    def logic(self, *reasons):
        for reason in reasons:
            assert reason.is_proved()
        assert self.is_sentence()
        atomics = {}
        reason_decompositions = []
        for reason in reasons:
            reason_decomposition, atomics = reason.logical_decomposition(atomics)
            reason_decompositions.append(reason_decomposition)
        self_decomposition, atomics = self.logical_decomposition(atomics)

        number_of_cases = (1 << len(atomics))
        for case in range(0, number_of_cases):
            truth = []
            for cursor in range(0, number_of_cases):
                if case & (1 << cursor):
                    truth.append(True)
                else:
                    truth.append(False)

            is_the_case = True
            for reason_decomposition in reason_decompositions:
                if not reason_decomposition.logical_evaluation(truth):
                    is_the_case = False
                    break
            if not is_the_case:
                continue

            assert self_decomposition.logical_evaluation(truth)
        
        self.prove_CAUTION()
        return self

    marked_names = None
    def by(self, *reasons, **arguments):
        first_call = False
        if Node.marked_names == None:
            first_call = True
            Node.marked_names = set()
        name = arguments.get("name")
        if name:
            assert not name in Node.marked_names
            Node.marked_names.add(name)
            function = Node.memory[name]
            node = function(self.copy(), *reasons)
            assert self.compare(node) and node.is_proved()
            if first_call:
                Node.marked_names = None
            else:
                Node.marked_names.remove(name)
            return node
        else:
            prefix = arguments.get("prefix")
            for key, function in Node.memory.items():
                if prefix and key[:len(prefix)] != prefix:
                    continue
                if key in Node.marked_names:
                    continue
                try:
                    Node.marked_names.add(key)
                    node = function(self.copy(), *reasons)
                    Node.marked_names.remove(key)
                    if node.is_proved() and self.compare(node):
                        if first_call:
                            Node.marked_names = None
                        return node
                except:
                    continue
            assert False

def remember(name, function):
    Node.memory[name] = function

def forget(name):
    del Node.memory[name]

def forget_prefix(prefix):
    for name in Node.memory.keys():
        if name[ : len(prefix)] == prefix:
            del Node.memory[name]

def verbose(switch):
    Node.verbose = switch

A = None
B = None
C = None
a = None
b = None
p = None
u = None
x = None
y = None
z = None
alpha = None

def clean_up():
    global A
    A = Variable("A")
    global B
    B = Variable("B")
    global C
    C = Variable("C")
    global a
    a = Variable("a")
    global b
    b = Variable("b")
    global p
    p = Variable("p")
    global u
    u = Variable("u")
    global x
    x = Variable("x")
    global y
    y = Variable("y")
    global z
    z = Variable("z")
    global alpha
    alpha = Variable("alpha")

# constructors
def _All(variable, bound, sentence):
    assert variable.is_variable()
    assert bound.is_sentence()
    assert sentence.is_sentence()
    return Node("quantifier", "all", [variable.copy(), bound.copy(), sentence.copy()], {})

def All(*arguments):
    sentence = arguments[-1]
    assert len(arguments) >= 3
    assert len(arguments) % 2 == 1
    node = sentence
    for index in reversed(range(0, len(arguments) - 1, 2)):
        node = _All(arguments[index], arguments[index + 1], node)
    return node

def _Exist(variable, bound, sentence):
    return Node("quantifier", "exist", [variable.copy(), bound.copy(), sentence.copy()], {})

def Exist(*arguments):
    sentence = arguments[-1]
    assert len(arguments) >= 3
    assert len(arguments) % 2 == 1
    node = sentence
    for index in reversed(range(0, len(arguments) - 1, 2)):
        node = _Exist(arguments[index], arguments[index + 1], node)
    return node

ID_counter = 0
def Variable(name, **attributes):
    global ID_counter
    ID_counter += 1
    return Node("variable", name + ("%05d" % ID_counter), [], attributes)

def Variable_namely(name, **attributes):
    global ID_counter
    ID_counter += 1
    return Node("variable", name, [], attributes)

def Function(name, **attributes):
    return Node("function", name, [], attributes)

def Property(name, **attributes):
    return Node("property", name, [], attributes)

def True_():
    return Node("logical", "true", [], {})

def False_():
    return Node("logical", "false", [], {})

# ... and so on



# axioms

# true
true = True_()
true.logic()
true.export("true")

# false
false = False_()
not_false = (~false).logic()
not_false.export("not_false")


# bound <=> assumption
def bound_to_assumption(target, source):
    return target.bound_to_assumption(source)

remember("booting::bound::1", bound_to_assumption)

def assumption_to_bound(target, source):
    return target.assumption_to_bound(source)

remember("booting::bound::2", assumption_to_bound)

# axiom scheme of equality
def equal(A_is_B, *reasons):
    for reason in reasons:
        assert reason.is_proved()
    assert A_is_B.is_property() and A_is_B.name == "equal" and len(A_is_B.children) == 2
    A = A_is_B[0]
    B = A_is_B[1]
    if not reasons:
        assert A.compare(B)
    else:
        assert A.equal(B, reason)
    A_is_B.prove_CAUTION()
    return A_is_B

remember("booting::equal::1", equal)

# set
clean_up()
definition_of_set, set_ = Exist(C, True_(), x @ C).say("set")
C_is_set = C.name
definition_of_set.export("set")

def is_set(target, source): # x in C => set_(x)
    x = source[0]
    C = source[1]
    P1 = Node.theorems["set"].put(x, true)
    C0 = P1.get_exist_variable()[0]
    P2 = (Exist(C0, true, x @ C0)).found(source, true, C)
    return set_(x).logic(P1, P2)

remember("booting::set::1", is_set)


# axiom of extensionality
clean_up()
extensionality = All(A, True_(), B, True_(), (All(x, set_(x), ((x @ A) // (x @ B))) >> (A == B)))
extensionality.prove_CAUTION()
extensionality.export("extensionality")

def uniqueness_from_extensionality(A, B, e, condition):
    with All(e, set_(e), (e @ A) // condition) as Ap:
        with All(e, set_(e), (e @ B) // condition) as Bp:
            x = Variable("x")
            P1 = ((x @ A) // (x @ B)).logic(Ap.put(x), Bp.put(x))
            P1 = P1.gen(x, set_(x))
            P2 = (A == B).logic(Node.theorems["extensionality"].put(A).put(B), P1)
        P2 = Node.last.copy()
    P2 = Node.last.copy()
    return P2

# axiom of pairing
clean_up()
pairing = All(x, set_(x), y, set_(y), Exist(p, set_(p), All(z, set_(z), (z @ p) // ((z == x) | (z == y)))))
pairing.prove_CAUTION()
pairing.export("axiom_of_pairing")
pairing, pairing_is_set, definition_of_pairing = pairing.let("pairing", binary = ",")
definition_of_pairing.export("existence_of_pairing")
pairing_is_set.export("pairing_is_set")

def Pairing(a, b):
    return Node("function", "pairing", [a.copy(), b.copy()], {"binary" : ","})

def OrderedPair(a, b):
    return Pairing(Pairing(a, b), b)

clean_up()
with set_(a) as ap:
    with set_(b) as bp:
        a_b_is_set = Node.theorems["pairing_is_set"].put(a, ap).put(b, bp)
        a_b_is_set = Node.theorems["pairing_is_set"].put(Pairing(a, b), a_b_is_set).put(b, bp)
    a_b_is_set = Node.last.copy()
    a_b_is_set = a_b_is_set.gen(b, true)
    a_b_is_set = All(b, set_(b), set_(OrderedPair(a, b))).by(a_b_is_set)
a_b_is_set = Node.last.copy()
a_b_is_set = a_b_is_set.gen(a, true)
a_b_is_set = All(a, set_(a), All(b, set_(b), set_(OrderedPair(a, b)))).by(a_b_is_set)
a_b_is_set.export("ordered_pairing_is_set")

def Tuple(*arguments):
    if len(arguments) == 0:
        return Variable("0_uple")
    elif len(arguments) == 1:
        return arguments[0].copy()
    else:
        result = arguments[0].copy()
        for argument in arguments[1 :]:
            result = OrderedPair(result, argument.copy())
        return result

def tuple_is_set(target, *arguments):
    variable_list = []
    for argument in arguments:
        variable_list.append(argument[0].copy())
    node = None
    sentence = None
    for index, variable in enumerate(variable_list):
        if index == 0:
            sentence = arguments[0]
            node = variable
        else:
            sentence = Node.theorems["ordered_pairing_is_set"].put(node, sentence).put(variable, arguments[index])
            node = OrderedPair(node, variable)
    return sentence

remember("booting::tuple::1", tuple_is_set)

# membership
E = Variable("E")
membership = Exist(E, true, All(x, set_(x), y, set_(y), (Tuple(x, y) @ E) // (x @ y)))
membership.prove_CAUTION()
membership_class, _ , membership = membership.let("membership")
membership.export("membership")

# intersection
intersection = All(A, true, B, true, Exist(C, true, All(x, set_(x), (x @ C) // ((x @ A) & (x @ B)))))
intersection.prove_CAUTION()
intersection_function, _, intersection = intersection.let("intersection")
intersection_function.set_("binary", "cap")
intersection.export("intersection")

def cap(A, B):
    return Node("function", "intersection", [A.copy(), B.copy()], {"binary" : "cap"})

def cap_law_1(target, source): # x in A cap B => x in A
    x = source[0]
    A = source[1][0]
    B = source[1][1]
    P = set_(x).by(source)
    return target.logic(Node.theorems["intersection"].put(A, true).put(B, true).put(x, P), source)

remember("booting::cap::1", cap_law_1)
    
def cap_law_2(target, source): # x in A cap B => x in B
    x = source[0]
    A = source[1][0]
    B = source[1][0]
    P = set_(x).by(source)
    return target.logic(Node.theorems["intersection"].put(A, true).put(B, true).put(x, P), source)

remember("booting::cap::2", cap_law_2)

def cap_law_3(target, source_A, source_B): # x in A, x in B => x in A cap B
    x = source_A[0]
    A = source_A[1]
    B = source_B[1]
    P = set_(x).by(source_A)
    return target.logic(Node.theorems["intersection"].put(A, true).put(B, true).put(x, P), source_A, source_B)

remember("booting::cap::3", cap_law_3)

def cap_law_4(target, source_B, source_A): # x in B, x in A => x in A cap B
    x = source_A[0]
    A = source_A[1]
    B = source_B[1]
    P = set_(x).by(source_A)
    return target.logic(Node.theorems["intersection"].put(A, true).put(B, true).put(x, P), source_A, source_B)

remember("booting::cap::4", cap_law_4)

# complement
complement = All(A, true, Exist(B, true, All(x, set_(x), ((x @ B) // ~(x @ A)))))
complement.prove_CAUTION()
complement_function, _, complement = complement.let("complement")
complement_function.set_("unary", "~")
complement.export("complement")

def complement_law_1(target, source): # x in A => ~(x in ~A)
    x = source[0]
    A = source[1]
    P = set_(x).by(source)
    return target.logic(Node.theorems["complement"].put(A, true).put(x, P), source)

remember("booting::complement::1", complement_law_1)

def complement_law_2(target, source): # x in ~A => ~(x in A)
    x = source[0]
    A = source[1][0]
    P = set_(x).by(source)
    return target.logic(Node.theorems["complement"].put(A, true).put(x, P), source)

remember("booting::complement::2", complement_law_2)

def complement_law_3(target, source, bound): # ~(x in A) & set(x) => x in ~A
    x = source[0][0]
    A = source[0][1]
    return target.logic(Node.theorems["complement"].put(A, true).put(x, bound), source)

remember("booting::complement::3", complement_law_3)

def complement_law_4(target, source, bound): # ~(x in ~A) & set(x) => x in A
    x = source[0][0]
    A = source[0][0][1]
    return target.logic(Node.theorems["complement"].put(A, true).put(x, bound), source)

remember("booting::complement::4", complement_law_4)

clean_up()
empty = membership_class & (~membership_class)
with (alpha @ empty) as P:
    alpha_in_E = (alpha @ membership_class).by(P)
    alpha_not_in_E = (~(alpha @ membership_class)).by((alpha @ ~membership_class).by(P))
    contradiction = false.logic(alpha_in_E, alpha_not_in_E)
P = (~(alpha @ empty)).logic(Node.last)
empty_has_no_elements = P.gen(alpha, set_(alpha))
empty_has_no_elements = (Exist(x, true, All(alpha, set_(alpha), ~(alpha @ x)))).found(empty_has_no_elements, true, empty)
empty_class, _, empty = empty_has_no_elements.let("empty")
empty.export("empty")

V = ~empty_class
with set_(alpha) as P:
    alpha_in_V = (alpha @ V).by(Node.theorems["empty"].put(alpha, P), P)
alpha_in_V = Node.last.copy()
alpha_in_V = alpha_in_V.gen(alpha, true)
alpha_in_V = (All(alpha, set_(alpha), (alpha @ V))).by(alpha_in_V)

alpha_in_V = (Exist(C, true, All(alpha, set_(alpha), alpha @ C))).found(alpha_in_V, true, V)
V, _, alpha_in_V = alpha_in_V.let("universe_V")
alpha_in_V.export("V_has_everything")

# domain
domain = All(A, true, Exist(B, true, All(x, set_(x), ((x @ B) // (Exist(y, set_(y), Tuple(x, y) @ A))))))
domain.prove_CAUTION()
domain_function, _, domain = domain.let("domain")
domain.export("domain")

# product by V
u = Variable("u")
product_by_V = All(A, true, Exist(B, true, All(u, set_(u), ((u @ B) // (Exist(x, set_(x), y, set_(y), (u == Tuple(x, y)) & (x @ A)))))))
product_by_V.prove_CAUTION()
product_by_V_function, _, product_by_V = product_by_V.let("product_by_V")
product_by_V.export("product_by_V")

# circular permutation
circular_permutation = All(A, true, Exist(B, true, All(x, set_(x), y, set_(y), z, set_(z), ((Tuple(x, y, z) @ B) // (Tuple(y, z, x) @ A)))))
circular_permutation.prove_CAUTION()
circular_permutation_function, _, circular_permutation = circular_permutation.let("circular_permutation")
circular_permutation.export("circular_permutation")

# transposition
transposition = All(A, true, Exist(B, true, All(x, set_(x), y, set_(y), z, set_(z), ((Tuple(x, y, z) @ B) // (Tuple(x, z, y) @ A)))))
transposition.prove_CAUTION()
transposition_function, _, transposition = transposition.let("transposition")
transposition.export("transposition")



# start
# TODO



