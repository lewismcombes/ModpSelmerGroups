# ModpSelmerGroups
Magma code to compute relaxed, nearly-ordinary and unramified Selmer groups associated to mod p Galois representations

Used in my thesis "Periods and Selmer groups associated to mod p Galois representations over imaginary quadratic fields".

Contains

 + conductor.m, to compute the conductor of a representation (only works for base field class number = 1)
 + character.m, to compute the character of a representation 
 + CFT_utility.m, containing some useful functions for Magma's class field theory computations 
 + NO_selmer_lines.m, which filters through a relaxed Selmer group and returns nearly-ordinary and unramified Selmer ranks 
 + NormalSubfields_K.m, some tweaks of Magma's code to compute normal subfields of a FldAb type 
 + get_rep.m, originally written by Aurel Page, turns a field extension into a Galois representation, computes Frobenius data, + other utility functions 
 + nearly_ordinary.m, which tells you if a given representation from get_rep.m is nearly-ordinary at a prime 
 + selmer_ranks.m, a loading script that returns the ranks of Selmer groups of the field extension given to it
