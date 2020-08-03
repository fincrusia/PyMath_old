import os
import sys
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

# pylint: disable=unused-wildcard-import
from node import *
from variables import *

# start!

def Set(x):
    return Node("property", "set", [x])

clean()
from variables import *
Exist(C, x @ C).define_property("set").export("definition_of_set")

print(theorems["definition_of_set"])
