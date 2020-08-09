import os
import sys
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

import pickle
import atexit
from itertools import permutations

# Node
class Node:
    __cursor = -1
    __branch = []
    __assumptions = []
    __non_generalizables = []
    last = None

    __logicals = ["and", "or", "not", "imply", "iff", "true", "false"]
    __quantifiers = ["all", "exist", "unique"]

    __memory = {}
    __names = set()

    binaries = {}
    pre_unaries = {}
    post_unaries = {}
    associatives = {}

    definitions = {}
    function_uniqueness = {}

    # basic
    def __init__(self, type_, name, children):
        if type_ == "logical":
            assert name in Node.__logicals
        elif type_ == "quantifier":
            assert name in Node.__quantifiers
        elif type_ == "atomic":
            assert isinstance(name, int)
        else:
            assert type_ in ["function", "property", "variable", "none"]

        self.__type = type_
        self.__name = name
        self.__children = children
        self.__branch = None
        Node.__names.add(name)

    def compare(self, A):
        if self.__type != A.__type:
            return False
        if self.__name != A.__name:
            return False
        if len(self) != len(A):
            return False
        for child_index in range(0, len(self)):
            if not self[child_index].compare(A[child_index]):
                return False
        return True

    def __equal(self, reason, A, B):
        if self.compare(reason):
            return True
        if self.compare(A) and reason.compare(B):
            return True
        if self.compare(B) and reason.compare(A):
            return True
        if self.__type != reason.__type:
            return False
        if self.__name != reason.__name:
            return False
        if len(self) != len(reason):
            return False
        for index in range(0, len(self)):
            if not self[index].__equal(reason[index], A, B):
                return False
        return True

    def equal(self, *reasons):
        if len(reasons) == 0:
            assert self.is_equal()
            assert self.left().compare(self.right())
            self.__prove()
            return self
        elif len(reasons) == 1:
            reason = reasons[0]
            assert reason.is_proved()
            assert self.compare(reason)
            self.__prove()
            return self
        else:
            assert len(reasons) == 2
            reason = reasons[0]
            assert reason.is_proved()
            A_is_B = reasons[1]
            assert A_is_B.is_proved()
            A = A_is_B.left()
            B = A_is_B.right()
            assert self.__equal(reason, A, B)
            self.__prove()
            return self

    def __str__(self):
        if self.is_quantifier():
            return self.__name + "(" + self.variable().__name + ":" + str(self.statement()) + ")"
        elif self.is_logical() or self.is_property() or self.is_function():
            if self.__name in Node.pre_unaries.keys():
                return "(" + Node.pre_unaries[self.__name] + " " + str(self.body()) + ")"
            elif self.__name in Node.post_unaries.keys():
                return "(" + str(self.body()) + " " + Node.post_unaries[self.__name] + ")"
            elif self.__name in Node.binaries.keys():
                return "(" + str(self.left()) + " " + Node.binaries[self.__name] + " " + str(self.right()) + ")"
            elif self.__name in Node.associatives.keys():
                result = "("
                for index, child in enumerate(self.__children):
                    result += str(child)
                    if index != len(self.__children) - 1:
                        result += Node.associatives[self.__name]
                result += ")"
                return result
            else:
                result = self.__name + "("
                for index, child in enumerate(self.__children):
                    result += str(child)
                    if index != len(self.__children) - 1:
                        result += ","
                result += ")"
                return result
        elif self.is_variable():
            return self.__name
        else:
            assert False
    
    # assumptions
    def __enter__(self):
        Node.__cursor += 1
        if len(Node.__branch) <= Node.__cursor:
            Node.__branch.append(0)
            Node.__assumptions.append(self)
            Node.__non_generalizables.append(self.get_free_names())
        else:
            Node.__branch[Node.__cursor] += 1
            Node.__assumptions[Node.__cursor] = self
            Node.__non_generalizables[Node.__cursor] = self.get_free_names()
        self.__prove()
        return self
    
    def __exit__(self, *arguments):
        Node.last = ((Node.__assumptions[Node.__cursor]) >> Node.last)
        Node.__cursor -= 1
        Node.last.__prove()
    
    # operators
    def __or__(self, A):
        if self.is_sentence():
            return Node("logical", "or", [self, A])
        elif self.is_term():
            return Node("function", "cup", [self, A])

    def __and__(self, A):
        if self.is_sentence():
            return Node("logical", "and", [self, A])
        elif self.is_term():
            return Node("function", "cap", [self, A])

    def __invert__(self):
        if self.is_sentence():
            return Node("logical", "not", [self])
        elif self.is_term():
            return Node("function", "complement", [self])

    def __rshift__(self, A):
        return Node("logical", "imply", [self, A])

    def __eq__(self, A):
        if A.is_none():
            return self.is_none()
        if self.is_sentence():
            return Node("logical", "iff", [self, A])
        elif self.is_term():
            return Node("property", "equal", [self, A])
    
    def __ne__(self, A):
        return ~(self == A)

    def __matmul__(self, A):
        return Node("property", "in", [self, A])
    
    def __lshift__(self, A):
        return Node("property", "inclusion", [self, A])

    def __call__(self, *arguments):
        if self.is_function() or self.is_property():
            return Node(self.__type, self.__name, arguments)
        else:
            children = [self]
            for argument in arguments:
                children.append(argument)
            return Node("function", "evaluation", children)

    def __getitem__(self, key):
        return self.__children[key]

    def __len__(self):
        return len(self.__children)

    # queries

    def get_name(self):
        return self.__name

    def get_type(self):
        return self.__type

    def is_proved(self):
        if self.__branch == None:
            return False
        if len(self.__branch) > Node.__cursor + 1:
            return False
        for cursor in range(0, len(self.__branch)):
            if self.__branch[cursor] != Node.__branch[cursor]:
                return False
        return True

    def is_generalizable(self):
        assert self.is_variable()
        for cursor in range(0, Node.__cursor + 1):
            if self.__name in Node.__non_generalizables[cursor]:
                return False
        return True

    def is_none(self):
        return self.__type == "none"

    def is_logical(self):
        return self.__type == "logical"

    def is_variable(self):
        return self.__type == "variable"

    def is_property(self):
        return self.__type == "property"
    
    def is_equal(self):
        return self.__type == "property" and self.__name == "equal" and len(self) == 2

    def is_function(self):
        return self.__type == "function"
    
    def is_quantifier(self):
        return self.__type == "quantifier"

    def is_term(self):
        if self.is_variable():
            return True
        elif self.is_function():
            for child in self.__children:
                if not child.is_term():
                    return False
            return True
        else:
            return False

    def is_sentence(self):
        if self.is_property():
            return True
        elif self.is_logical():
            for child in self.__children:
                if not child.is_sentence():
                    return False
            return True
        elif self.is_quantifier():
            return self.variable().is_variable() and self.statement().is_sentence()
        else:
            return False

    def __is_readable(self, bounded_names):
        if self.is_quantifier() and self.__name in bounded_names:
            return False
        else:
            if self.is_quantifier():
                bounded_names in set([self.__name])
            for child in self.__children:
                if not child.__is_readable(bounded_names):
                    return False
            return True

    def is_readable(self):
        return self.is_sentence() and self.__is_readable(set())

    def is_closed(self):
        return self.is_sentence() and not self.get_free_names()

    # access
    def body(self):
        assert len(self) == 1
        return self[0]
    
    def variable(self):
        assert self.is_quantifier()
        return self[0]
    
    def statement(self):
        assert self.is_quantifier()
        return self[1]

    def left(self):
        assert len(self) == 2
        return self[0]
    
    def right(self):
        assert len(self) == 2
        return self[1]

    def name(self):
        return self.__name

    # APIs
    def __get_free_names(self, bounded_names):
        if self.is_variable() and not self.__name in bounded_names:
            return set([self.__name])
        if self.is_quantifier():
            bounded_names |= set([self.variable().__name])
        free_names = set()
        for child in self.__children:
            free_names |= child.__get_free_names(bounded_names)
        return free_names

    def get_free_names(self):
        return self.__get_free_names(set())

    def __substitute(self, variable, term):
        if self.is_variable() and self.__name == variable.__name:
            return term
        elif self.is_quantifier() and self.variable().__name in term.get_free_names():
            assert False # for readability
        else:
            children = [child.__substitute(variable, term) for child in self.__children]
            return Node(self.__type, self.__name, children)

    def substitute(self, variable, term):
        assert variable.is_variable()
        assert term.is_term()
        return self.__substitute(variable, term)

    def __contract(self, term, variable):
        if self.compare(term):
            return variable
        elif self.is_quantifier() and self.variable().__name in term.get_free_names():
            assert False # for readability
        else:
            children = [child.__contract(term, variable) for child in self.__children]
            return Node(self.__type, self.__name, children)

    def contract(self, term, variable):
        assert term.is_term()
        assert variable.is_variable()
        return self.__contract(term, variable)

    def __logical_decomposition(self, atomics):
        if self.is_logical():
            children = []
            for child in self.__children:
                child_decomposition, atomics = child.__logical_decomposition(atomics)
                children.append(child_decomposition)
            return Node(self.__type, self.__name, children), atomics
        else:
            for key, atomic in atomics.items():
                if self.compare(atomic):
                    return Node("atomic", key, []), atomics
            atomics[len(atomics)] = self
            return Node("atomic", len(atomics) - 1, []), atomics
    
    def __logical_evaluation(self, truth):
        if self.__type == "atomic":
            return truth[self.__name]
        else:
            assert self.is_logical()
            if self.__name == "and":
                return self.left().__logical_evaluation(truth) and self.right().__logical_evaluation(truth)
            elif self.__name == "or":
                return self.left().__logical_evaluation(truth) or self.right().__logical_evaluation(truth)
            elif self.__name == "not":
                return not self.body().__logical_evaluation(truth)
            elif self.__name == "imply":
                return (not self.left().__logical_evaluation(truth)) or self.right().__logical_evaluation(truth)
            elif self.__name == "iff":
                return self.left().__logical_evaluation(truth) == self.right().__logical_evaluation(truth)
            elif self.__name == "true":
                return True
            elif self.__name == "false":
                return False
            else:
                assert False

    def get_exist_variables(self):
        result = []
        if self.is_quantifier and self.__name == "exist":
            result.append(self.variable())
        for child in self.__children:
            for exist_variable in child.get_exist_variables():
                result.append(exist_variable)
        return result

    def get_all_variables(self):
        result = []
        if self.is_quantifier and self.__name == "all":
            result.append(self.variable())
        for child in self.__children:
            for exist_variable in child.get_all_variables():
                result.append(exist_variable)
        return result
    

    # prove
    def __prove(self):
        assert self.is_readable()
        self.__branch = [x for x in Node.__branch[ : Node.__cursor + 1]]
        Node.last = self
        return self
    
    def export(self, name):
        assert self.is_proved()
        assert not self.__branch
        assert self.is_closed()
        theorems[name] = self
        #print(self) # verbose

    def put(self, term):
        assert self.is_proved()
        assert term.is_term()
        assert self.is_quantifier() and self.__name == "all"

        variable = self.variable()
        sentence = self.statement().substitute(variable, term)
        sentence.__prove()
        return sentence

    def bput(self, term, bound):
        assert self.is_proved()
        assert bound.is_proved()
        variable = self.variable()
        return self.statement().right().substitute(variable, term).logic(bound, self.put(term))

    def assert_unique(self, variable):
        assert self.is_proved()
        assert self.is_quantifier() and self.__name == "all"
        assert self.statement().is_quantifier() and self.statement().__name == "all"
        a = self.variable()
        b = self.statement().variable()
        assert a.is_variable()
        assert b.is_variable()
        statement = self.statement().statement()
        assert statement.is_logical() and statement.__name == "imply"
        assumption = statement.left()
        conclusion = statement.right()
        assert assumption.is_logical() and assumption.__name == "and"
        left = assumption.left()
        right = assumption.right()
        assert left.substitute(a, b).compare(right)
        assert conclusion.compare(a == b)
        uniqueness = Unique(variable, left.substitute(a, variable))
        uniqueness.__prove()
        return uniqueness

    def expand_unique(self, a, b):
        assert self.is_proved()
        assert self.is_quantifier() and self.__name == "unique"
        variable = self.variable()
        left = self.substitute(variable, a)
        right = self.substitute(variable, b)
        return (left & right) >> (a == b)

    define_function_counter = 0
    def define_function(self, name):
        Node.define_function_counter += 1
        assert not name in Node.__names
        assert self.is_proved()

        arguments = []
        cursor = self
        bounds = []
        while cursor.is_quantifier() and cursor.__name == "all":
            arguments.append(cursor.variable())
            cursor = cursor.statement()
            if cursor.is_logical() and cursor.__name == "imply":
                bounds.append(cursor.left())
                cursor = cursor.right()
            else:
                bounds.append(NoneNode("DF"))
        
        assert cursor.is_logical() and cursor.__name == "and"
        left = cursor.left()
        right = cursor.right()
        assert left.is_quantifier()
        assert right.is_quantifier()
        assert (left.__name == "exist" and right.__name == "unique") or (left.__name == "unique" and right.__name == "exist")
        a = left.variable()
        b = right.variable()
        assert left.statement().substitute(a, b).compare(right.statement())
        new_function = Function(name)
        new_term = new_function(*arguments)
        definition = left.statement().substitute(a, new_term)

        # uniqueness part
        DF = Variable("DF_" + str(Node.define_function_counter))
        uniqueness = All(DF, definition.contract(new_term, DF) >> (DF == new_term))
        
        for index in reversed(range(0, len(arguments))):
            if bounds[index] == NoneNode("DF"):
                uniqueness = All(arguments[index], uniqueness)
            else:
                uniqueness = All(arguments[index], bounds[index] >> uniqueness)
        uniqueness.__prove()

        Node.function_uniqueness[name] = uniqueness

        for index in reversed(range(0, len(arguments))):
            if bounds[index] == NoneNode("DF"):
                definition = All(arguments[index], definition)
            else:
                definition = All(arguments[index], bounds[index] >> definition)
        definition.__prove()
        Node.definitions[name] = definition

        return definition

    __let_counter = 0
    def let(self, name):
        assert self.is_quantifier() and self.__name == "exist"
        exist_variable = self.variable()
        Node.__let_counter += 1
        assert not name in Node.__names
        let_variable = Variable(name)
        statement = self.statement().substitute(exist_variable, let_variable)
        statement.__prove()
        return statement

    __found_term = None
    __found_variable = None
    def __found(self, reason):
        if self.compare(reason):
            return True
        elif self.compare(Node.__found_variable):
            if Node.__found_term:
                return reason.compare(Node.__found_term)
            else:
                Node.__found_term = self
                return True
        else:
            if self.__type != reason.__type:
                return False
            if self.__name != reason.__name:
                return False
            if len(self) != len(reason.__children):
                return False
            for index in range(0, len(self)):
                if not self[index].__found(reason[index]):
                    return False
            return True

    def found(self, reason):
        Node.__found_term = None
        assert self.is_quantifier() and self.__name == "exist"
        assert reason.is_proved()
        Node.__found_variable = self.variable()
        assert self.statement().__found(reason)
        self.__prove()
        return self

    def gen(self, variable):
        assert self.is_proved()
        assert variable.is_generalizable()
        result = All(variable, self)
        result.__prove()
        return result

    def define_property(self, name):
        assert self.is_sentence()
        assert not name in Node.__names
        free_names = self.get_free_names()
        new_property = Property(name)
        free_variables = []
        for free_name in free_names:
            free_variables.append(Variable(free_name))
        definition = (new_property(*free_variables) == self)
        for free_variable in reversed(free_variables):
            definition = All(free_variable, definition)
        definition.__prove()
        Node.definitions[name] = definition
        return definition

    def logic(self, *reasons):
        for reason in reasons:
            assert reason.is_proved()
        assert self.is_sentence()
        atomics = {}
        reason_decompositions = []
        for reason in reasons:
            reason_decomposition, atomics = reason.__logical_decomposition(atomics)
            reason_decompositions.append(reason_decomposition)
        self_decomposition, atomics = self.__logical_decomposition(atomics)

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
                if not reason_decomposition.__logical_evaluation(truth):
                    is_the_case = False
                    break
            if not is_the_case:
                continue
            assert self_decomposition.__logical_evaluation(truth)
        
        self.__prove()
        return self

    def not_exist_to_all_not(self):
        assert self.is_proved()
        assert self.is_logical() and self.__name == "not"
        cursor = self.body()
        assert cursor.is_quantifier() and cursor.__name == "exist"
        variable = cursor.variable()
        cursor = cursor.statement()
        all_not = All(variable, ~cursor)
        all_not.__prove()
        return all_not

    def not_all_exist_not(self):
        assert self.is_proved()
        assert self.is_logical() and self.__name == "not"
        cursor = self.body()
        assert cursor.is_quantifier() and cursor.__name == "all"
        variable = cursor.variable()
        cursor = cursor.statement()
        exist_not = Exist(variable, ~cursor)
        exist_not.__prove()
        return exist_not

    __marked_indexes = set()
    choices = {}
    def by(self, *reasons):
        form = str(self)
        for reason in reasons:
            form += ("\\\\" + str(reason))
        if Node.choices.get(form):
            try:
                index, permute = Node.choices[form]
                assert len(reasons) == len(permute)
                reasons_permuted = [reasons[permute[x]] for x in range(0, len(reasons))]
                target = inferences[index](self, *reasons_permuted)
                assert target.is_proved()
                assert self.compare(target)
                return target
            except:
                del Node.choices[form]
        permutations_list = list(permutations(range(0, len(reasons))))
        for permute in permutations_list:
            for index, inference in enumerate(inferences):
                if index in Node.__marked_indexes:
                    continue
                try:
                    reasons_permuted = [reasons[permute[x]] for x in range(0, len(reasons))]
                    Node.__marked_indexes.add(index)
                    target = inference(self, *reasons_permuted)
                    assert target.is_proved()
                    assert self.compare(target)
                    if index in Node.__marked_indexes:
                        Node.__marked_indexes.remove(index)
                    Node.choices[form] = (index, permute)
                    return target
                except:
                    if index in Node.__marked_indexes:
                        Node.__marked_indexes.remove(index)
        assert False

    def axiom(self):
        self.__prove()
        return self

theorems = {}

# load choices
choices_file_name = "choices.pickle"
try:
    with open(choices_file_name, "rb") as fp:
        Node.choices = pickle.load(fp)
except:
    Node.choices = {}

def dump():
    with open(choices_file_name, "wb") as fp:
        pickle.dump(Node.choices, fp)

atexit.register(dump)

# inferences
inferences = []


def pre_unary(name, operator):
    Node.pre_unaries[name] = operator

def post_unary(name, operator):
    Node.post_unaries[name] = operator

def binary(name, operator):
    Node.binaries[name] = operator

def associative(name, operator):
    Node.associatives[name] = operator

def All(variable, statement):
    return Node("quantifier", "all", [variable, statement])

def Exist(variable, statement):
    return Node("quantifier", "exist", [variable, statement])

def Unique(variable, statement):
    return Node("quantifier", "unique", [variable, statement])

def Property(name):
    return Node("property", name, [])

def Function(name):
    return Node("function", name, [])

def Variable(name):
    return Node("variable", name, [])

def NoneNode(name):
    return Node("none", name, [])

def remember(inference):
    inferences.append(inference)

def escape(*arguments):
    if not arguments:
        return Node.last
    else:
        assert len(arguments) == 1
        argument = arguments[0]
        return Node.last.gen(argument)

def composite_function(name, term, *arguments):
    A = Variable("CF_0")
    B = Variable("CF_1")
    C = Variable("CF_2")
    D = Variable("CF_3")
    existence = Exist(C, C == term).found((term == term).by())
    with A == term as At:
        with B == term as Bt:
            (A == B).by(At, Bt)
    uniqueness = (((A == term) & (B == term)) >> (A == B)).by(escape())
    uniqueness = uniqueness.gen(B).gen(A)
    uniqueness = uniqueness.assert_unique(D)
    uniquely_exist = (uniqueness & existence).by(uniqueness, existence)
    for argument in reversed(arguments):
        uniquely_exist = uniquely_exist.gen(argument)
    definition = uniquely_exist.define_function(name)
    return definition

def get_definition(name):
    return Node.definitions[name]

def get_uniqueness(name):
    return Node.function_uniqueness[name]

