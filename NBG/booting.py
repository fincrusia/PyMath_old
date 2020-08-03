import os
import sys
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

# pylint: disable=unused-wildcard-import
from node import *
from variables import *

# start!

clean()

def logic(target, sources):
    return target.logic(sources)

remember(logic)

def Set(x):
    return Node("property", "set", [x])

from variables import *
Exist(C, x @ C).define_property("set").export("definition_of_set")

print(theorems["definition_of_set"])

def is_set(target, reason): # x in C => Set(x)
    x = reason.left()
    definition_of_set = theorems["definition_of_set"]
    C0 = definition_of_set.get_exist_variables()[0]
    xs = Set(x).logic(Exist(C0, x @ C0).found(reason), definition_of_set.put(x))
    return xs

remember(is_set)