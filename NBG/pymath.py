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
                if not self[cursor].equal(A[cursor], reason):
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
            return self.name    
            #return self.name[:-5]
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

    def __ne__(self, A):
        return Node("logical", "not", [(self.copy() == A.copy())], {})
    
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

    found_term = None
    def _found(self, reason, variable):
        if self.compare(reason):
            return True
        elif self.compare(variable):
            if Node.found_term:
                if reason.compare(Node.found_term):
                    return True
            else:
                assert reason.is_term()
                Node.found_term = reason.copy()
                return True
        else:
            assert len(self.children) == len(reason.children)
            for index in range(0, len(self.children)):
                if not self[index]._found(reason[index], variable):
                    return False
            return True

    def found(self, reason, bound):
        Node.found_term = None
        assert self.is_quantifier() and self.name == "exist"
        assert reason.is_proved()
        assert bound.is_proved()
        variable = self[0].copy()
        assert self[1]._found(bound, variable)
        assert self[2]._found(reason, variable)
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
        #print("******")
        #print(self)
        #print(Node("quantifier", source.name, [x, new_bound, sentence], {}))
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
            Node.marked_names.remove(name)
            if first_call:
                Node.marked_names = None
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
                    if key in Node.marked_names:
                        Node.marked_names.remove(key)
                    if node.is_proved() and self.compare(node):
                        if first_call:
                            Node.marked_names = None
                        return node
                except:
                    if key in Node.marked_names:
                        Node.marked_names.remove(key)
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
c = None
p = None
u = None
x = None
y = None
z = None
alpha = None

def clean():
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
    global c
    c = Variable("c")
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

def escape(variable):
    N = Node.last.copy()
    P = N.gen(variable, true)
    Q = All(variable, P[2][0], P[2][1]).by(P)
    return Q

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
        reason.is_proved()
    reason = None
    if reasons:
        reason = reasons[0]
    assert A_is_B.is_property() and A_is_B.name == "equal" and len(A_is_B.children) == 2
    A = A_is_B[0]
    B = A_is_B[1]
    if not reason:
        assert A.compare(B)
    else:
        assert A.equal(B, reason)
    A_is_B.prove_CAUTION()
    return A_is_B

remember("booting::equal::1", equal)

def equivalent(target, source, A_is_B):
    assert source.is_proved()
    assert A_is_B.is_proved()
    assert A_is_B.is_property() and A_is_B.name == "equal"
    assert target.equal(source, A_is_B)
    target.prove_CAUTION()
    return target

remember("booting::equal::2", equivalent)

# set
clean()
definition_of_set, set_ = Exist(C, True_(), x @ C).say("set")
C_is_set = C.name
definition_of_set.export("set")

def is_set(target, source): # x in C => set_(x)
    x = source[0]
    C = source[1]
    P1 = Node.theorems["set"].put(x, true)
    C0 = P1.get_exist_variable()[0]
    P2 = (Exist(C0, true, x @ C0)).found(source, true)
    return set_(x).logic(P1, P2)

remember("booting::set::1", is_set)


# axiom of extensionality
clean()
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
clean()
pairing = All(x, set_(x), y, set_(y), Exist(p, set_(p), All(z, set_(z), (z @ p) // ((z == x) | (z == y)))))
pairing.prove_CAUTION()
pairing.export("axiom_of_pairing")
pairing, pairing_is_set, definition_of_pairing = pairing.let("pairing", binary = "..")
definition_of_pairing.export("definition_of_pairing")
pairing_is_set.export("pairing_is_set")

def Pairing(a, b):
    return Node("function", "pairing", [a.copy(), b.copy()], {"binary" : ".."})

empty = None
def FiniteSet(*arguments):
    if len(arguments) == 0:
        return empty
    elif len(arguments) == 1:
        return arguments[0].copy()
    else:
        node = arguments[0].copy()
        for argument in arguments[1:]:
            node = Pairing(node, argument.copy())
        return node

def finite_set_is_set(target, *arguments):
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
            Node.theorems["pairing_is_set"].put(node, sentence)
            sentence = Node.theorems["pairing_is_set"].put(node, sentence).put(variable, arguments[index])
            node = Pairing(node, variable)
    return sentence

remember("booting::pairing::1", finite_set_is_set)


# x in {a, b} => x == a or x == b
def expand_pairing(target, source, *bounds):
    x = source[0]
    ab = source[1]
    a = ab[0]
    b = ab[1]
    a_s = bounds[0]
    bs = bounds[1]
    xs = set_(x).by(source)
    P = Node.theorems["definition_of_pairing"].put(a, a_s).put(b, bs).put(x, xs)
    return ((x == a) | (x == b)).logic(source, P)

remember("booting::pairing::4", expand_pairing)


def OrderedPair(a, b):
    return Pairing(Pairing(a, b), b)

clean()
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
        return empty
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

# empty set
clean()
empty = membership_class & (~membership_class)
with (alpha @ empty) as P:
    alpha_in_E = (alpha @ membership_class).by(P)
    alpha_not_in_E = (~(alpha @ membership_class)).by((alpha @ ~membership_class).by(P))
    contradiction = false.logic(alpha_in_E, alpha_not_in_E)
P = (~(alpha @ empty)).logic(Node.last)
empty_has_no_elements = P.gen(alpha, set_(alpha))
empty_has_no_elements = (Exist(x, true, All(alpha, set_(alpha), ~(alpha @ x)))).found(empty_has_no_elements, true)
empty_class, _, empty = empty_has_no_elements.let("empty")
empty.export("empty")

# has element => not empty
def has_element_so_not_empty(target, source):
    x = source[0]
    A = source[1]
    with A == empty_class as Ae:
        xs = set_(x).by(source)
        P = Node.theorems["empty"].put(x, xs)
        #print(source)
        #print(Ae)
        Q = (x @ empty_class).by(source, Ae)
        false.logic(P, Q)
    R = (~(A == empty_class)).logic(Node.last.copy())
    return R

remember("booting::empty::1", has_element_so_not_empty)

# V
V = ~empty_class
with set_(alpha) as P:
    alpha_in_V = (alpha @ V).by(Node.theorems["empty"].put(alpha, P), P)
alpha_in_V = Node.last.copy()
alpha_in_V = alpha_in_V.gen(alpha, true)
alpha_in_V = (All(alpha, set_(alpha), (alpha @ V))).by(alpha_in_V)

alpha_in_V = (Exist(C, true, All(alpha, set_(alpha), alpha @ C))).found(alpha_in_V, true)
V, _, alpha_in_V = alpha_in_V.let("universe_V")
alpha_in_V.export("V_has_everything")

# domain
clean()
domain = All(A, true, Exist(B, true, All(x, set_(x), ((x @ B) // (Exist(y, set_(y), Tuple(x, y) @ A))))))
domain.prove_CAUTION()
domain_function, _, domain = domain.let("domain")
domain.export("domain")

# product by V
clean()
product_by_V = All(A, true, Exist(B, true, All(u, set_(u), ((u @ B) // (Exist(x, set_(x), y, set_(y), (u == Tuple(x, y)) & (x @ A)))))))
product_by_V.prove_CAUTION()
product_by_V_function, _, product_by_V = product_by_V.let("product_by_V")
product_by_V.export("product_by_V")

# circular permutation
clean()
circular_permutation = All(A, true, Exist(B, true, All(x, set_(x), y, set_(y), z, set_(z), ((Tuple(x, y, z) @ B) // (Tuple(y, z, x) @ A)))))
circular_permutation.prove_CAUTION()
circular_permutation_function, _, circular_permutation = circular_permutation.let("circular_permutation")
circular_permutation.export("circular_permutation")

# transposition
clean()
transposition = All(A, true, Exist(B, true, All(x, set_(x), y, set_(y), z, set_(z), ((Tuple(x, y, z) @ B) // (Tuple(x, z, y) @ A)))))
transposition.prove_CAUTION()
transposition_function, _, transposition = transposition.let("transposition")
transposition.export("transposition")

# regularity
clean()
regularity = All(a, set_(a), (a != empty_class) >> Exist(u, set_(u), (u @ a) & ((u & a) == empty_class)))
regularity.prove_CAUTION()
regularity.export("regularity")

# theorem : (x, x) == {x}
clean()
with set_(x) as xs:
    a = Pairing(x, x)
    a_s = set_(a).by(xs, xs)
    with set_(y) as ys:
        P1 = Node.theorems["definition_of_pairing"].put(x, xs).put(x, xs).put(y, ys)
        ((y @ a) // (y == x)).logic(P1)
    P2 = Node.last.copy()
    P3 = P2.gen(y, true)
    P4 = (All(y, set_(y), ((y @ a) // (y == x)))).by(P3)
P5 = Node.last.copy()
P6 = P5.gen(x, true)
P7 = All(x, set_(x), All(y, set_(y), ((y @ a) // (y == x)))).by(P6)
P7.export("set_envelope")

# theorem : no Quine
clean()
with set_(x) as xs:
    with x @ x as xp:
        a = Pairing(x, x)
        a_s = set_(a).by(xs, xs)
        P1 = Node.theorems["definition_of_pairing"].put(x, xs).put(x, xs).put(a, a_s)
        P3 = (x == x).by()
        P2 = Node.theorems["set_envelope"].put(x, xs).put(x, xs)
        x_in_a = (x @ a).logic(P2, P3)
        x_in_x_cap_a = (x @ (x & a)).by(xp, x_in_a)
        P4 = Node.theorems["regularity"].put(a, a_s)
        a_is_not_empty = (~(a == empty_class)).by(x_in_a)
        P5 = P4[1].logic(a_is_not_empty, P4)
        zf, zb, zs = P5.let("no_Quine_temporary")
        P6 = (zf @ a).logic(zs)
        P7 = Node.theorems["set_envelope"].put(x, xs).put(zf, zb)
        P8 = (zf == x).logic(P6, P7)
        P9 = ((x @ a) & ((x & a) == empty_class)).by(zs, P8)
        x_cap_a_is_empty = ((x & a) == empty_class).logic(P9)
        x_cap_a_is_not_empty = (~((x & a) == empty_class)).by(x_in_x_cap_a)
        false.logic(x_cap_a_is_empty, x_cap_a_is_not_empty)
    no_Quine = (~(x @ x)).logic(Node.last.copy())
no_Quine = Node.last.copy().gen(x, true)
no_Quine = All(x, set_(x), ~(x @ x)).by(no_Quine)
no_Quine.export("no_Quine")

# set(a), set(b) => a in Pairing(a, b)
def in_pairing_a(target, a_s, bs):
    a = a_s[0]
    b = bs[0]
    P = Node.theorems["definition_of_pairing"].put(a, a_s).put(b, bs).put(a, a_s)
    a_is_a = (a == a).by()
    return (a @ Pairing(a, b)).logic(a_is_a, P)

remember("booting::pairing::2", in_pairing_a)


# set(a), set(b) => b in Pairing(a, b)
def in_pairing_b(target, a_s, bs):
    a = a_s[0]
    b = bs[0]
    P = Node.theorems["definition_of_pairing"].put(a, a_s).put(b, bs).put(b, bs)
    b_is_b = (b == b).by()
    return (b @ Pairing(a, b)).logic(b_is_b, P)

remember("booting::pairing::3", in_pairing_b)


# axiom of union
clean()
punion = All(a, set_(a), Exist(b, set_(b), All(x, set_(x), (Exist(y, set_(y), (x @ y) & (y @ a))) >> (x @ b))))
punion.prove_CAUTION()
punion_function, punion_bound, punion_sentence = punion.let("primitive_union", unary = "pcup")
punion_sentence.export("definition_of_punion")
punion_bound.export("punion_is_set")

def PUnion(x):
    return Node("function", "primitive_union", [x.copy()], {"unary" : "pcup"})

def PBinaryUnion(a, b):
    return PUnion(Pairing(a, b))

# (x in a or x in b) => x in (a cup b) 
clean()
with set_(a) as a_s:
    with set_(b) as bs:
        ab_s = set_(Pairing(a, b)).by(a_s, bs)
        a_pcub_b_s = Node.theorems["punion_is_set"].put(Pairing(a, b), ab_s)
        a_pcup_b = Node.theorems["definition_of_punion"].put(Pairing(a, b), ab_s)

        with x @ a as xa:
            xs = set_(x).by(xa)
            y0 = a_pcup_b.get_exist_variable()[0]
            P1 = a_pcup_b.put(x, xs)
            a_in_ab = (a @ Pairing(a, b)).by(a_s, bs)
            x_in_a_in_ab = ((x @ a) & (a @ Pairing(a, b))).logic(xa, a_in_ab)
            P2 = Exist(y0, set_(y0), (x @ y0) & (y0 @ Pairing(a, b))).found(x_in_a_in_ab, a_s)
            P3 = (x @ PBinaryUnion(a, b)).logic(P1, P2)
        P4 = Node.last.copy()

        with x @ b as xb:
            xs = set_(x).by(xb)
            y0 = a_pcup_b.get_exist_variable()[0]
            P1 = a_pcup_b.put(x, xs)
            b_in_ab = (b @ Pairing(a, b)).by(a_s, bs)
            x_in_b_in_ab = ((x @ b) & (b @ Pairing(a, b))).logic(xb, b_in_ab)
            P2 = Exist(y0, set_(y0), (x @ y0) & (y0 @ Pairing(a, b))).found(x_in_b_in_ab, bs)
            P3 = (x @ PBinaryUnion(a, b)).logic(P1, P2)
        P5 = Node.last.copy()

        P6 = ((P4[0].copy() | P5[0].copy()) >> P4[1].copy()).logic(P4, P5)
        P6 = P6.gen(x, set_(x))

    P7 = Node.last.copy().gen(b, true)
    All(b, set_(b), P7[2][1]).by(P7, name = "booting::bound::2")
P8 = Node.last.copy().gen(a, true)
P9 = All(a, set_(a), P8[2][1]).by(P8)
P9.export("property_of_binary_punion")


# x in A => A != empty
def has_something_then_not_empty(target, source):
    x = source[0]
    A = source[1]
    xs = set_(x).by(source)
    with A == empty_class as Ae:
        P1 = Node.theorems["empty"].put(x, xs)
        P2 = (~(x @ A)).by(P1, Ae)
        false.logic(source, P2)
    P3 = (~(A == empty_class)).logic(Node.last.copy())
    return P3

remember("booting::empty::2", has_something_then_not_empty)


# x in y and y in x => contradiction
clean()
with set_(x) as xs:
    with set_(y) as ys:
        with x @ y as x_in_y:
            with y @ x as y_in_x:
                P1 = Node.theorems["definition_of_pairing"].put(x, xs).put(y, ys)
                u = Pairing(x, y)
                us = set_(u).by(xs, ys)
                P2 = Node.theorems["regularity"].put(u, us)
                x_in_u = (x @ u).by(xs, ys)
                y_in_u = (y @ u).by(xs, ys)
                xy_is_not_empty = (~(u == empty_class)).by(x_in_u)
                P3 = P2[1].logic(P2, xy_is_not_empty)
                kf, kb, kc = P3.let("no_circular_inclusion_temp") # to be modified
                P4 = Node.theorems["definition_of_pairing"].put(x, xs).put(y, ys).put(kf, kb)
                P5 = ((kf == x) | (kf == y)).logic(P4, kc)
                with kf == x as kx:
                    P6 = ((kf & u) == empty_class).logic(kc)
                    P7 = ((x & u) == empty_class).by(P6, kx)
                    P8 = (y @ (x & u)).by(y_in_u, y_in_x)
                    P9 = ((x & u) != empty_class).by(P8)
                    false.logic(P7, P9)
                P10 = (kf != x).logic(Node.last.copy())
                P11 = (kf == y).logic(P5, P10)
                P6 = ((kf & u) == empty_class).logic(kc)
                P7 = ((y & u) == empty_class).by(P6, P11)
                P8 = (x @ (y & u)).by(x_in_u, x_in_y)
                P9 = ((y & u) != empty_class).by(P8)
                false.logic(P7, P9)
            P12 = Node.last.copy()
        P13 = Node.last.copy()
        P14 = (~((x @ y) & (y @ x))).logic(P13)
    P15 = Node.last.copy().gen(y, true)
    P16 = All(y, set_(y), P15[2][1]).by(P15)
P17 = Node.last.copy().gen(x, true)
P18 = All(x, set_(x), P17[2][1]).by(P17)
P18.export("no_cyclic_inclusion")


# a == b => b == a
def reflection_of_equality(target, source):
    a = source[0]
    b = source[1]
    bb = (b == b).by()
    ba = (b == a).by(bb, source)
    return ba

remember("booting::equal::3", reflection_of_equality)


# a != b => b != a
def reflection_of_nequality(target, source):
    a = source[0][0]
    b = source[0][1]
    with b == a as ba:
        ab = (a == b).by(ba)
        false.logic(ab, source)
    nba = (b != a).logic(Node.last.copy())
    return nba

remember("booting::equal::4", reflection_of_nequality)

# (a, b) == (x, y) => (a == x and b == y)
clean()
ab = Tuple(a, b)
xy = Tuple(x, y)
with set_(a) as a_s:
    with set_(b) as bs:
        with set_(x) as xs:
            with set_(y) as ys:
                with ab == xy as source:
                    ab_s = set_(ab).by(a_s, bs)
                    uab = Pairing(a, b)
                    uabs = set_(uab).by(a_s, bs)
                    a_in_uab = (a @ uab).by(a_s, bs)
                    b_in_uab = (b @ uab).by(a_s, bs)
                    uab_in_ab = (uab @ ab).by(uabs, bs)
                    b_in_ab = (b @ ab).by(uabs, bs)
                    
                    xys = set_(xy).by(xs, ys)
                    uxy = Pairing(x, y)
                    uxys = set_(uxy).by(xs, ys)
                    x_in_uxy = (x @ uxy).by(xs, ys)
                    y_in_uxy = (y @ uxy).by(xs, ys)
                    uxy_in_xy = (uxy @ xy).by(uxys, ys)
                    y_in_xy = (y @ xy).by(uxys, ys)

                    b_in_xy = (b @ xy).by(b_in_ab, source)
                    y_in_ab = (y @ ab).by(y_in_xy, source)

                    P = Node.theorems["definition_of_pairing"].put(uxy, uxys).put(y, ys).put(b, bs)
                    P = ((b == y) | (b == uxy)).logic(P, b_in_xy)

                    Q = Node.theorems["definition_of_pairing"].put(uab, uabs).put(b, bs).put(y, ys)
                    Q = ((y == b) | (y == uab)).logic(Q, y_in_ab)

                    with b != y as nby:
                        P = (b == uxy).logic(P, nby)
                        with y == b as yb:
                            by = (b == y).by(yb)
                            false.logic(by, nby)
                        nyb = (y != b).logic(Node.last.copy())
                        Q = (y == uab).logic(Q, nyb)

                        y_in_b = (y @ b).by(y_in_uxy, P)
                        b_in_y = (b @ y).by(b_in_uab, Q)

                        false.logic(y_in_b, b_in_y, Node.theorems["no_cyclic_inclusion"].put(b, bs).put(y, ys))
                    
                    by = (b == y).logic(Node.last.copy())

                    with b == uab as b_uab:
                        b_not_in_b = Node.theorems["no_Quine"].put(b, bs)
                        b_in_b = (b @ b).by(b_in_uab, b_uab)
                        false.logic(b_not_in_b, b_in_b)
                    n_b_uab = (b != uab).logic(Node.last.copy())
                    
                    with y == uxy as y_uxy:
                        y_not_in_y = Node.theorems["no_Quine"].put(y, ys)
                        y_in_y = (y @ y).by(y_in_uxy, y_uxy)
                        false.logic(y_not_in_y, y_in_y)
                    n_y_uxy = (y != uxy).logic(Node.last.copy())

                    uab_in_ab = (uab @ ab).by(uabs, bs)
                    uab_in_xy = (uab @ xy).by(uab_in_ab, source)
                    uab_x_or_y = ((uab == uxy) | (uab == y)).by(uab_in_xy, uxys, ys)
                    n_y_uab = (y != uab).by(n_b_uab, by)
                    n_uab_y = (uab != y).by(n_y_uab, name = "booting::equal::4")

                    uab_uxy = (uab == uxy).logic(uab_x_or_y, n_uab_y)

                    a_uxy = (a @ uxy).by(a_in_uab, uab_uxy)
                    ax_or_ay = ((a == x) | (a == y)).by(a_uxy, xs, ys)

                    x_uab = (x @ uab).by(x_in_uxy, uab_uxy)
                    xa_or_xb = ((x == a) | (x == b)).by(x_uab, a_s, bs)

                    with a != x as nax:
                        a_y = (a == y).logic(nax, ax_or_ay)
                        a_b = (a == b).by(a_y, by)
                        xa_or_xa = ((x == a) | (x == a)).by(xa_or_xb, a_b)
                        xa = (x == a).logic(xa_or_xa)
                        ax = (a == x).by(xa)
                        false.logic(ax, nax)
                    a_x = (a == x).logic(Node.last.copy())

                    result = ((a == x) & (b == y)).logic(a_x, by)
                result = Node.last.copy()
            node = Node.last.copy()[1]
            result = Node.last.copy().gen(y, true)
            result = All(y, set_(y), node).by(result)
        node = Node.last.copy()[1]
        result = Node.last.copy().gen(x, true)
        result = All(x, set_(x), node).by(result)
    node = Node.last.copy()[1]
    result = Node.last.copy().gen(b, true)
    result = All(b, set_(b), node).by(result)
node = Node.last.copy()[1]
result = Node.last.copy().gen(a, true)
result = All(a, set_(a), node).by(result)
result.export("ordered_pairing_compare")

def tuple_compare(target, source, *bounds):
    arity = len(bounds) // 2
    
    variable_list_1 = [bound[0] for bound in bounds[:arity]]
    variable_list_2 = [bound[0] for bound in bounds[arity:]]

    if arity == 2:
        P = Node.theorems["ordered_pairing_compare"].put(variable_list_1[0], bounds[0]).put(variable_list_1[1], bounds[1])
        P = P.put(variable_list_2[0], bounds[2]).put(variable_list_2[1], bounds[3])
        P = P[1].logic(P, source)
        return P

    node_list_1 = []
    node_list_2 = []

    bound_list_1 = []
    bound_list_2 = []

    node_1 = None
    node_2 = None
    for index in range(0, arity):
        if index == 0:
            node_1 = variable_list_1[index]
            node_2 = variable_list_2[index]
            bound_list_1.append(set_(node_1).by(bounds[index]))
            bound_list_2.append(set_(node_2).by(bounds[index + arity]))
        else:
            _node_1 = OrderedPair(node_1, variable_list_1[index])
            _node_2 = OrderedPair(node_2, variable_list_2[index])

            bound_list_1.append(set_(_node_1).by(bound_list_1[index - 1], bounds[index]))
            bound_list_2.append(set_(_node_2).by(bound_list_2[index - 1], bounds[index + arity]))
 
            node_1 = _node_1
            node_2 = _node_2


        node_list_1.append(node_1)
        node_list_2.append(node_2)

    sentence = source
    conclusion = None
    P = Node.theorems["ordered_pairing_compare"]
    for index in reversed(range(1, arity)):
        Q = P.put(node_list_1[index - 1], bound_list_1[index - 1]).put(variable_list_1[index], bounds[index])
        Q = Q.put(node_list_2[index - 1], bound_list_2[index - 1]).put(variable_list_2[index], bounds[index + arity])
        Q = Q[1].logic(sentence, Q)
        sentence = Q
        
        if index == arity - 1:
            conclusion = sentence[1].copy().logic(sentence)
        elif index == 1:
            conclusion = (conclusion & sentence[1]).logic(conclusion, sentence)
            conclusion = (conclusion & sentence[0]).logic(conclusion, sentence)
        else:
            conclusion = (conclusion & sentence[1]).logic(conclusion, sentence)

    return conclusion

remember("booting::tuple::2", tuple_compare)


# tuple lemma
clean()
with set_(x) as xs:
    with set_(y) as ys:
        with set_(z) as zs:
            xyz = Tuple(x, y, z)
            xyz_is_set = set_(xyz).by(xs, ys, zs)
            xy = OrderedPair(x, y)
            P1 = Node.theorems["product_by_V"].put(A, true).put(xyz, xyz_is_set)
            x0, y0 = P1.get_exist_variable()
            xys = set_(xy).by(xs, ys)
            with xyz @ product_by_V_function(A) as xyz_in_AV:
                P2 = Exist(x0, set_(x0), Exist(y0, set_(y0), ((xyz == Tuple(x0, y0)) & (x0 @ A)))).logic(P1, xyz_in_AV)
                x0_function, x0_bound, sentence = P2.let("tuple_lemma_x0")
                y0_function, y0_bound, sentence = sentence.let("tuple_lemma_y0")
                P3 = (xyz == Tuple(x0_function, y0_function)).logic(sentence)
                xyz_x0y0 = ((xy == x0_function) & (z == y0_function)).by(P3, xys, zs, x0_bound, y0_bound, name = "booting::tuple::2")
                xy_x0 = xyz_x0y0[0].logic(xyz_x0y0)
                sentence = sentence[1].copy().logic(sentence)
                sentence = (xy @ A).by(sentence, xy_x0)
            P4 = Node.last.copy()

            with xy @ A as xy_in_A:
                xyz_is_xyz = (xyz == xyz).by()
                P5 = (xyz_is_xyz & xy_in_A).logic(xyz_is_xyz, xy_in_A)
                P6 = Exist(y0, set_(y0), (xyz == Tuple(xy, y0)) & (xy @ A)).found(P5, zs)
                P7 = Exist(x0, set_(x0), Exist(y0, set_(y0), (xyz == Tuple(x0, y0)) & (x0 @ A))).found(P6, xys)
                P8 = P1[0].copy().logic(P1, P7)
            P9 = Node.last.copy()

            P10 = (P4[0] // P4[1]).logic(P4, P9)
        escape(z)
    escape(y)
escape(x).gen(A, true).export("tuple_lemma_3")


clean()
with set_(x) as xs:
    with set_(y) as ys:
        with set_(z) as zs:
            P1 = Node.theorems["tuple_lemma_3"].put(A, true).put(x, xs).put(y, ys).put(z, zs)
            P2 = Node.theorems["transposition"].put(product_by_V_function(A), true).put(x, xs).put(z, zs).put(y, ys)
            P3 = (P2[0] // P1[1]).logic(P1, P2)
        escape(z)
    escape(y)
escape(x).gen(A, true).export("tuple_lemma_2")


clean()
with set_(x) as xs:
    with set_(y) as ys:
        with set_(z) as zs:
            P1 = Node.theorems["tuple_lemma_3"].put(A, true).put(x, xs).put(y, ys).put(z, zs)
            P2 = Node.theorems["circular_permutation"].put(product_by_V_function(A), true).put(z, zs).put(x, xs).put(y, ys)
            P3 = (P2[0] // P1[1]).logic(P1, P2)
        escape(z)
    escape(y)
escape(x).gen(A, true).export("tuple_lemma_1")

# added
clean()
with set_(x) as xs:
    with set_(y) as ys:
        with set_(z) as zs:
            T = transposition_function(product_by_V_function(A))
            P1 = Node.theorems["tuple_lemma_2"].put(A, true).put(x, xs).put(y, ys).put(z, zs)
            P2 = Node.theorems["circular_permutation"].put(T, true).put(y, ys).put(x, xs).put(z, zs)
            P3 = (P2[0] // P1[1]).logic(P1, P2)
        escape(z)
    escape(y)
escape(x).gen(A, true).export("tuple_lemma_5")


clean()
with set_(x) as xs:
    with set_(y) as ys:
        with set_(z) as zs:
            yx = Tuple(y, x)
            yxs = set_(yx).by(ys, xs)
            xy = Tuple(x, y)
            xys = set_(xy).by(xs, ys)
            B = (transposition_function(product_by_V_function(A)))
            C = circular_permutation_function(B)
            D = domain_function(C)
            Q1 = Node.theorems["domain"].put(C, true).put(yx, yxs)
            with yx @ D as yx_D:
                Q2 = Q1[1].logic(Q1, yx_D)
                f, fb, fc = Q2.let("tuple_lemma_temp")
                P1 = Node.theorems["tuple_lemma_2"].put(A, true).put(x, xs).put(y, ys).put(f, fb)
                P2 = Node.theorems["circular_permutation"].put(B, true).put(y, ys).put(x, xs).put(f, fb)
                P3 = (P2[0] // P1[1]).logic(P1, P2)
                xy_A = (xy @ A).logic(fc, P3)
            xy_D_to_xy_A = Node.last.copy()
            with xy @ A as xy_A:
                CTP = circular_permutation_function(transposition_function(product_by_V_function(A)))
                Q3 = Node.theorems["tuple_lemma_5"].put(A, true).put(x, xs).put(y, ys).put(z, zs)
                y0 = Q1.get_exist_variable()[0]
                Q6 = Q3[0].logic(Q3, xy_A)
                Q4 = Exist(y0, set_(y0), Tuple(y, x, y0) @ CTP).found(Q6, zs)
                Q5 = Q1[0].logic(Q1, Q4)
            xy_A_to_xy_D = Node.last.copy()
            conclusion = ((yx @ D) // (xy @ A)).logic(xy_D_to_xy_A, xy_A_to_xy_D)
        escape(z)
    escape(y)
escape(x).gen(A, true).export("tuple_lemma_4")




# start
# TODO



