import os
import sys
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from node import Variable


clean_counter = 0
def clean():
    global clean_counter
    clean_counter += 1

    global a
    a = Variable("a" + str(clean_counter))
    global b
    b = Variable("b" + str(clean_counter))
    global c
    c = Variable("c" + str(clean_counter))
    global d
    d = Variable("d" + str(clean_counter))
    global e
    e = Variable("e" + str(clean_counter))
    global f
    f = Variable("f" + str(clean_counter))
    global g
    g = Variable("g" + str(clean_counter))
    global h
    h = Variable("h" + str(clean_counter))
    global i
    i = Variable("i" + str(clean_counter))
    global j
    j = Variable("j" + str(clean_counter))
    global k
    k = Variable("k" + str(clean_counter))
    global l
    l = Variable("l" + str(clean_counter))
    global m
    m = Variable("m" + str(clean_counter))
    global n
    n = Variable("n" + str(clean_counter))
    global o
    o = Variable("o" + str(clean_counter))
    global p
    p = Variable("p" + str(clean_counter))
    global q
    q = Variable("q" + str(clean_counter))
    global r
    r = Variable("r" + str(clean_counter))
    global s
    s = Variable("s" + str(clean_counter))
    global t
    t = Variable("t" + str(clean_counter))
    global u
    u = Variable("u" + str(clean_counter))
    global v
    v = Variable("v" + str(clean_counter))
    global w
    w = Variable("w" + str(clean_counter))
    global x
    x = Variable("x" + str(clean_counter))
    global y
    y = Variable("y" + str(clean_counter))
    global z
    z = Variable("z" + str(clean_counter))

    global A
    A = Variable("A" + str(clean_counter))
    global B
    B = Variable("B" + str(clean_counter))
    global C
    C = Variable("C" + str(clean_counter))
    global D
    D = Variable("D" + str(clean_counter))
    global E
    E = Variable("E" + str(clean_counter))
    global F
    F = Variable("F" + str(clean_counter))
    global G
    G = Variable("G" + str(clean_counter))
    global H
    H = Variable("H" + str(clean_counter))
    global I
    I = Variable("I" + str(clean_counter))
    global J
    J = Variable("J" + str(clean_counter))
    global K
    K = Variable("K" + str(clean_counter))
    global L
    L = Variable("L" + str(clean_counter))
    global M
    M = Variable("M" + str(clean_counter))
    global N
    N = Variable("N" + str(clean_counter))
    global O
    O = Variable("O" + str(clean_counter))
    global P
    P = Variable("P" + str(clean_counter))
    global Q
    Q = Variable("Q" + str(clean_counter))
    global R
    R = Variable("R" + str(clean_counter))
    global S
    S = Variable("S" + str(clean_counter))
    global T
    T = Variable("T" + str(clean_counter))
    global U
    U = Variable("U" + str(clean_counter))
    global V
    V = Variable("V" + str(clean_counter))
    global W
    W = Variable("W" + str(clean_counter))
    global X
    X = Variable("X" + str(clean_counter))
    global Y
    Y = Variable("Y" + str(clean_counter))
    global Z
    Z = Variable("Z" + str(clean_counter))