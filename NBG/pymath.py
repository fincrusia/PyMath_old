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
        if self.branch:
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

    def equal(self, A, reason):
        assert reason.is_property and len(reason.children) == 2
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
            return ("(" + self.name + "(" + str(self[0]) + "," + str(self[1]) + "," + str(self[2]) + "))")
        elif self.is_property() or self.is_function():
            if self["unary"]:
                assert len(self.children) == 1
                return ("(" + self["unary"] + " " + str(self[0]) + ")")
            elif self["binary"]:
                assert len(self.children) == 2
                return ("(" + str(self[0]) + " " + self["binary"] + " " + str(self[1]) + ")")
            else:
                result = ("(" + self.name + "(")
                for index, child in enumerate(self.children):
                    result += str(child)
                    if index != len(self.children) - 1:
                        result += ","
                result += "))"
                return result
        elif self.is_variable():
            return self.name

    def _repr(self, IDs):
        if self.is_variable():
            if not IDs.get(self.name):
                IDs[self.name] = len(IDs) + 1
            return ("#" + str(IDs[self.name]))
        else:
            result = "(" + self.name + "("
            for child in self.children:
                result += (str(child) + ",")
            result += "))"
            return result

    def __repr__(self):
        result, _ = self._repr({})
        return result


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
        return self.copy()

    def __exit__(self, *arguments):
        Node.last = (Node.assumptions[Node.cursor].copy() >> Node.last.copy())
        Node.cursor -= 1

    
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
            return Node("function", "intersection", [self.copy(), A.copy()], {"binary" : "cup"})
        else:
            assert False

    def __invert__(self):
        return Node("logical", "not", [self.copy()], {})

    def __rshift__(self, A):
        return Node("logical", "imply", [self.copy(), A.copy()], {})

    def __floordiv__(self, A):
        return Node("logical", "iff", [self.copy(), A.copy()], {})

    def __eq__(self, A):
        return Node("property", "equal", [self.copy(), A.copy()], {})
    
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
        elif self.type in Node.quantifiers and self.children[0].ID == variable.ID:
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
            return Node(self.name(), self.type, children, self.attributes)

    def contract(self, term, variable):
        assert term.is_term()
        assert variable.is_variable()
        free_names = term.get_free_names()
        return self._contract(term, variable, free_names)

    def logical_decomposition(self, atomics):
        if self.is_logical():
            children = [child._logical_decomposition(atomics) for child in self.children]
            return Node(self.type, self.name, children, {}), atomics
        else:
            for key, atomic in atomics.items():
                if self.compare(atomic):
                    return Node("atomic", key, [], {})
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

        result = _All(variable, bound_put, sentence_put)
        result.prove_CAUTION()
        return result

    def found(self, term, bound, name):
        assert self.is_proved()
        assert term.is_term()
        assert bound.is_proved()
        assert not name in Node.names

        variable = Variable(name)
        bound_found = bound.contract(term, variable)
        sentence_found = self.contract(term, variable)

        result = _Exist(variable, bound_found, sentence_found)
        result.prove_CAUTION()
        return result

    def let(self, name):
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

        new_function = Function(name)

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
            free_variables.append(Variable(free_name))
        node = (new_property(*free_variables) // self.copy())
        for free_variable in reversed(free_variables):
            node = _All(free_variable, True_(), node)
        node.prove_CAUTION()
        return node, new_property.copy()

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

    def by(self, *reasons, **arguments):
        name = arguments.get("name")
        if name:
            function = Node.memory[name]
            function(self.copy(), *reasons)
            return self
        else:
            prefix = arguments.get("prefix")
            for key, function in Node.memory.items():
                if prefix and key[:len(prefix)] != prefix:
                    continue
                try:
                    function(self.copy(), *reasons)
                    if self.is_proved():
                        return self
                except:
                    pass



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
    for index in range(0, len(arguments) - 1, 2):
        node = _All(arguments[index], arguments[index + 1], node)
    return node

def _Exist(variable, bound, sentence):
    return Node("quantifier", "exist", [variable.copy(), bound.copy(), sentence.copy()], {})

def Exist(*arguments):
    sentence = arguments[-1]
    assert len(arguments) >= 3
    assert len(arguments) % 2 == 1
    node = sentence
    for index in range(0, len(arguments) - 1, 2):
        node = _Exist(arguments[index], arguments[index + 1], node)
    return node

def Variable(name, **attributes):
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
verbose(True)

# true
true = True_()
true.logic()
true.export("true")

# axiom scheme of equality
def equal(A_is_B, reason):
    assert reason.is_proved()
    assert A_is_B.is_property() and A_is_B.name == "equal" and len(A_is_B.children) == 2
    A = A_is_B[0]
    B = A_is_B[1]
    assert A.equal(B, reason)
    A_is_B.prove()
remember("equal", equal)

# set
x = Variable("x")
C = Variable("C")
definition_of_set, set_ = Exist(C, True_(), x @ C).say("set")
definition_of_set.export("set")

# axiom of extensionality
A = Variable("A")
B = Variable("B")
extensionality = All(A, True_(), B, True_(), (All(x, set_(x), ((x @ A) // (x @ B))) >> (A == B)))
extensionality.prove_CAUTION()
extensionality.export("extensionality")

# axiom of pairing
y = Variable("y")
p = Variable("p")
z = Variable("z")
pairing = All(x, set_(x), y, set_(y), Exist(p, set_(p), All(z, set_(z), (z @ p) // ((z == x) | (z == y)))))
pairing.prove_CAUTION()
pairing.export("pairing")
definition_of_pairing, pairing = pairing.say("pairing")

def Pairing(a, b):
    return Node("function", "pairing", [a.copy(), b.copy()], {"binary" : "cup"})

def OrderedPair(a, b):
    return Pairing(a, Pairing(a, b))

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

# membership
E = Variable("E")
membership = Exist(E, true, All(x, set_(x), y, set_(y), (Tuple(x, y) @ E) // (x @ y)))
membership.prove_CAUTION()
membership_class, _ , membership = membership.let("membership")
membership.export("membership")

# intersection
intersection = All(A, true, B, true, Exist(C, true, All(x, set_(x), (x @ C) // ((x @ A) and (x @ B)))))
intersection.prove_CAUTION()
intersection_function, _, intersection = intersection.let("intersection")
intersection_function.set_("binary", "cap")
intersection.export("intersection")

def Intersection(A, B):
    return Node("function", "intersection", [A.copy(), B.copy()], {"binary" : "cap"})

# complement
complement = All(A, true, Exist(B, true, All(x, set_(x), ((x @ B) // ~(x @ A)))))
complement.prove_CAUTION()
complement_function, _, complement = complement.let("complement")
complement.export("complement")

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



