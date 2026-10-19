This is code for the paper **Full automorphism groups of the axial algebra for $M_{11}$ and related algebras**: 
http://arxiv.org/abs/2602.07556.
The main file with the various routines used is Automorphisms.m, while examples for the 
large algebras corresponding to $M_{11}$, the maximal subgroups $M_{10}$, and $L_2(11)$ 
are included as ASCII text. These can be read using eval Read();. For these algebras, if 
its dimension is n (for instance for $M_{11}$, $n=286$) then the MAGMA data file is A_n. 
In a MAGMA session we can just read off as :
>A := eval Read("A_286");

The Frobenius form for the algebras $A_n$ is in an ASCII text file "form_n", and can be read off again
using the same command. The files with the computations for $A_n$ are in the files "A_n.m",
 and can just be loaded in a MAGMA session using
>load "A_286.m";

again using $n=286$ as an example. 

The Computation 7.11 is included in a standalone file: "Computation_7_11.m". 

Various log files can be found for typical output in the logs subdirectory. 
