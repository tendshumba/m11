// A_76.m  --  Section 5 of the revised paper: the 76-dimensional algebra for A_6
//
// Rearranged (October 2026) to follow the computations of the revised paper, in order:
//   Computation 5.1  (a) G = Aut(M) = A_6.2^2 acts on A, (b) no Jordan axes, (c) no twins,
//                    (d) no involution of G outside M corresponds to an axis
//   Computation 5.2  joint eigenspace decomposition with respect to Y
//   Computation 5.3  (a) unique form on U, (b) U_N and the idempotent d, (c) d unique of length 2 in U,
//                    (d) spectrum of ad_d on A and U, (e) almost Monster law AM(1/2,1/8)
//   Remark 5.4       tau_d is an involution of G outside M; the G-images of d generate A
//   Computation 5.5  U' = U_0(d), W' = U_{1/8}(d): (a) u_1,u_2,u_3, (b) generate U', (c) <<W'>> = U,
//                    (d) 1-dimensional extension space, (e) nonzero product
//   Computation 5.7  (a) eigenvalue 1/5 of u_i on W_i only, (b) extension spaces, (c) <<W_1,W_2,W_3>> = A,
//                    (d) nonzero products
//
// Run from the directory containing Automorphisms.m and A_76:   magma A_76.m
// Output goes to A_76.log. Runs in minutes on a laptop.

SetSeed(1);
Attach("Automorphisms.m");
SetVerbose("Automorphisms", 0);
SetLogFile("A_76.log" : Overwrite := true);
t_start := Cputime();
Section := procedure(name, t0)
   printf "\n================ %o ================\n", name;
end procedure;
Timed := procedure(label, t0)
   printf "   [%o: %o s]\n", label, Cputime(t0);
end procedure;
// diagonalisability test for a rational matrix: the eigenspaces span the whole space
IsDiag := func< M | &+[Dimension(Eigenspace(M, e[1])) : e in Eigenvalues(M)] eq Nrows(M) >;

Section("Setup", t_start);
t0 := Cputime();
A := eval Read("A_76");
Timed("reading the data file -> A", t0);
F := BaseField(A);
axes := [A.i : i in [1..76] | IsIdempotent(A.i)];
assert #axes eq 45;
t0 := Cputime();
assert HasMonsterFusionLaw(axes[1]);
Timed("Monster fusion law check", t0);
t0 := Cputime();
Miy_p, Miy, isom, gpname := MiyamotoGroup(axes);
Timed("Miyamoto group -> Miy_p, Miy, isom, gpname", t0);
print "Miyamoto group:", gpname;
M := Miy;
// The Frobenius form. Its uniqueness up to scale follows from Corollary 3.6 of the paper (no Jordan axes,
// Computation 5.1(b), and M = A_6 simple); here we only compute a form to work with, normalised by (a,a) = 1.
// The form is read from the file form_76 if present; otherwise it is computed and written to form_76.
try
   t0 := Cputime();
   form := eval Read("form_76");
   Timed("reading the data file -> form", t0);
   print "Frobenius form read from form_76.";
catch err
   print "form_76 not found; computing the Frobenius form.";
   t0 := Cputime();
   bool, forms := HasFrobeniusForm(A);
   Timed("space of Frobenius forms -> forms", t0);
   assert bool and Dimension(forms) eq 1;
   form := Matrix(F, 76, 76, Eltseq(forms.1));
   form := 1/LengthOfElement(axes[1], form)*form;
   PrintFileMagma("form_76", form : Overwrite := true);
   print "Frobenius form written to form_76.";
end try;
assert IsAssociatingForm(A, form);
assert LengthOfElement(axes[1], form) eq 1;

// The Klein four-group E of Miyamoto involutions inside a Sylow 2-subgroup of M, and the axes Y
T_syl := SylowSubgroup(Miy, 2);
assert GroupName(T_syl) eq "D4";
subs4 := Subgroups(T_syl : OrderEqual := 4);
assert exists(i){ i : i in [1..#subs4] | GroupName(subs4[i]`subgroup) eq "C2^2"};
Y := {@ y : y in axes | TauMapMonster(y) in subs4[i]`subgroup @};
assert #Y eq 3;
// the axes in Y pairwise generate 2A (so they do not associate; cf. Subsection 3.2)
assert Y[1]*Y[2] eq 1/8*(Y[1]+Y[2]-Y[3]);
assert Y[1]*Y[3] eq 1/8*(Y[1]-Y[2]+Y[3]);
assert Y[2]*Y[3] eq 1/8*(-Y[1]+Y[2]+Y[3]);
E := sub< Miy | [TauMapMonster(x) : x in Y] >;
assert GroupName(E) eq "C2^2";

Section("Computation 5.1", t_start);
// (a) the group of automorphisms of A preserving the axet is G = Aut(M) = A_6.2^2
t0 := Cputime();
Gp, G := GroupFromAxes(axes);
Timed("group of automorphisms preserving the axet -> Gp, G", t0);
assert GroupName(Gp) in {"A6.C2^2", "S6.C2"};
assert Order(G) eq 1440;
print "Computation 5.1(a): the group of known automorphisms is G of order 1440, G =", GroupName(Gp);
// (b) no Jordan axes
t0 := Cputime();
jordans := JordanAxes(A, [Matrix(x) : x in Generators(Miy)] : form := form);
Timed("search for Jordan axes -> jordans", t0);
assert #jordans eq 0;
print "Computation 5.1(b): A has no Jordan axes.";
// (c) no twins
t0 := Cputime();
twins := FindTwins(axes[1] : form := form);
Timed("search for twins -> twins", t0);
assert #twins eq 0;
print "Computation 5.1(c): the 45 axes have no twins.";
// (d) the involutions of G outside M (classes of sizes 30 and 36) are not induced by axes
invsG := [x : x in ConjugacyClasses(G) | x[1] eq 2];
assert #invsG eq 3;
assert exists(i_45){i : i in [1..3] | #Class(G, invsG[i][3]) eq 45};
assert exists(i_30){i : i in [1..3] | #Class(G, invsG[i][3]) eq 30};
assert exists(i_36){i : i in [1..3] | #Class(G, invsG[i][3]) eq 36};
t0 := Cputime();
bool := IsInducedFromAxis(A, Matrix(invsG[i_30][3]) : form := form, automorphism_check := false);
Timed("search for axes inducing the involution -> bool", t0);
assert not bool;
t0 := Cputime();
bool := IsInducedFromAxis(A, Matrix(invsG[i_36][3]) : form := form, automorphism_check := false);
Timed("search for axes inducing the involution -> bool", t0);
assert not bool;
print "Computation 5.1(d): the involutions of G in the classes of sizes 30 and 36 are not induced by axes.";

Section("Computation 5.2", t_start);
t0 := Cputime();
decomps := JointEigenspaceDecomposition(Y);
Timed("joint eigenspace decomposition -> decomps", t0);
assert Keys(decomps) eq {[0,0,0], [1/4,1/32,1/32], [1/32,1/4,1/32], [1/32,1/32,1/4],
                         [0,1/32,1/32], [1/32,0,1/32], [1/32,1/32,0]};
U := decomps[[0,0,0]];
assert Dimension(U) eq 15;
assert forall{x : x in [[1/4,1/32,1/32], [1/32,1/4,1/32], [1/32,1/32,1/4]] | Dimension(decomps[x]) eq 5};
assert forall{x : x in [[0,1/32,1/32], [1/32,0,1/32], [1/32,1/32,0]] | Dimension(decomps[x]) eq 11};
assert Dimension(&+[decomps[x] : x in Keys(decomps)]) eq 63;   // the joint eigenspaces do not span A (dim 76)
W1 := decomps[[0, 1/32, 1/32]];
W2 := decomps[[1/32, 0, 1/32]];
W3 := decomps[[1/32, 1/32, 0]];
print "Computation 5.2: dim U = 15; 1/4-components of dimension 5; W_1, W_2, W_3 of dimension 11; the sum of the joint eigenspaces has dimension 63 < 76.";

Section("Computation 5.3", t_start);
t0 := Cputime();
Ualg := Algebra< F, 15 | AllStructureConstants(FindStructureConstantsSubalgebra(A, U)) >;
Timed("structure constants of the subalgebra -> Ualg", t0);
form_U := RestrictedForm(form, U);
// (a) U admits a unique Frobenius form up to scale
t0 := Cputime();
bool, forms_U := HasFrobeniusForm(Ualg);
Timed("space of Frobenius forms -> forms_U", t0);
assert bool and Dimension(forms_U) eq 1;
print "Computation 5.3(a): the space of Frobenius forms on U is 1-dimensional.";
// (b) the subalgebra U_N of fixed points of N = N_G(E) on U has dimension 5 and contains exactly 24 idempotents
//     over the algebraic closure; among them a unique one, d, of length 2, which is rational
N := Normaliser(G, E);
assert Order(N) eq 48;    // N = 2 x S_4
gensN := SetToSequence(Generators(N));
gensN_U := [x : x in {@ RestrictMapToSubspace(Matrix(g), U) : g in gensN @} | not IsIdentity(x)];
t0 := Cputime();
U_N := FindFixedSubalgebra(Ualg, gensN_U);
Timed("fixed subalgebra -> U_N", t0);
assert Dimension(U_N) eq 5;
t0 := Cputime();
idemps_UN := FindAllIdempotents(Ualg, U_N);
Timed("idempotent search (Groebner basis) -> idemps_UN", t0);
assert Type(idemps_UN) ne MonStgElt;
assert #idemps_UN eq 24;
// lengths of the 24 idempotents; the set may live over the algebraic closure if some of them are irrational,
// so the form is evaluated over the field the idempotents are defined over
Len := func< y | (Matrix(Vector(y)) * ChangeRing(form_U, BaseRing(Parent(y))) * Transpose(Matrix(Vector(y))))[1,1] >;
twos_in_UN := [y : y in idemps_UN | Len(y) eq 2];
assert #twos_in_UN eq 1;
d := Ualg![F!c : c in Eltseq(twos_in_UN[1])];     // the unique one is rational (fixed by the Galois group)
assert IsIdempotent(d) and LengthOfElement(d, form_U) eq 2;
printf "   lengths of the 24 idempotents of U_N: %o\n", Sort([Len(y) : y in idemps_UN | IsCoercible(F, Len(y))]);
print "Computation 5.3(b): dim U_N = 5; U_N has 24 idempotents over the algebraic closure, exactly one, d, of length 2, and d is rational.";
// (c) d is the only idempotent of length 2 in U over the algebraic closure
t0 := Cputime();
twos_in_U := FindAllIdempotents(Ualg, VectorSpace(Ualg) : length := 2, form := form_U);
Timed("idempotent search (Groebner basis) -> twos_in_U", t0);
assert Type(twos_in_U) ne MonStgElt and #twos_in_U eq 1;
assert Ualg!twos_in_U[1] eq d;
print "Computation 5.3(c): d is the only idempotent of length 2 in U (over the algebraic closure).";
// (d) ad_d is diagonalisable on A and on U with the stated eigenvalues and multiplicities
ad_d := AdMat(d);
d_A := A!(d@BasisMatrix(U));
assert IsIdempotent(d_A);
ad_dA := AdMat(d_A);
assert IsDiag(ad_dA) and IsDiag(ad_d);   // stated in 5.3(d); the fusion law check in (e) implies it again
assert Eigenvalues(ad_dA) eq {<1,1>, <0,34>, <1/2,9>, <1/8,32>};
assert Eigenvalues(ad_d) eq {<1,1>, <0,7>, <1/2,3>, <1/8,4>};
print "Computation 5.3(d): ad_d diagonalisable; eigenvalues 1, 0, 1/2, 1/8 of multiplicities 1, 34, 9, 32 on A and 1, 7, 3, 4 on U.";
// (e) d satisfies the almost Monster type fusion law AM(1/2, 1/8) in U and in A
SetVerbose("Fusion_check", 0);
t0 := Cputime();
assert HasAlmostMonsterFusionLaw(d : arbitrary_parameters := <1/2, 1/8>);
Timed("fusion law check", t0);
t0 := Cputime();
assert HasAlmostMonsterFusionLaw(d_A : arbitrary_parameters := <1/2, 1/8>);
Timed("fusion law check", t0);
print "Computation 5.3(e): d satisfies AM(1/2,1/8) in U and in A.";

Section("Remark 5.4", t_start);
z := TauMap(d_A, <[1, 0, 1/2], [1/8]>);
assert z in G;
assert z in Class(G, invsG[i_30][3]);
assert not z in Miy;
d_ims := Vector(d_A)^G;
assert #d_ims eq 30;
t0 := Cputime();
assert Dimension(Subalgebra({@ A!x : x in d_ims @})) eq 76;
Timed("subalgebra generated", t0);
assert GroupName(sub< G | Class(G, invsG[i_30][3]) >) eq "S6";
print "Remark 5.4: tau_d = z lies in the class of 30 involutions of G outside M; the 30 G-images of d generate A; the class generates S_6.";

Section("Computation 5.5", t_start);
// U' := U_0(d) (dimension 7) and W' := U_{1/8}(d) (dimension 4)
Up := Eigenspace(ad_d, 0);
assert Dimension(Up) eq 7;
Wp := Eigenspace(ad_d, 1/8);
assert Dimension(Wp) eq 4;
t0 := Cputime();
Up_alg := Algebra< F, 7 | AllStructureConstants(FindStructureConstantsSubalgebra(Ualg, Up)) >;
Timed("structure constants of the subalgebra -> Up_alg", t0);
form_Up := RestrictedForm(form_U, Up);
// (a) over the algebraic closure, U' has exactly three idempotents of length 17/5, and they are rational
t0 := Cputime();
idemps_17_5 := FindAllIdempotents(Up_alg, VectorSpace(Up_alg) : length := 17/5, form := form_Up);
Timed("idempotent search (Groebner basis) -> idemps_17_5", t0);
assert Type(idemps_17_5) ne MonStgElt and #idemps_17_5 eq 3;
assert forall{v : v in idemps_17_5 | IsCoercible(Up_alg, v)};
us := [Up_alg!v : v in idemps_17_5];
print "Computation 5.5(a): U' has exactly three idempotents u_1, u_2, u_3 of length 17/5 over the algebraic closure; all rational.";
// (b) <<u_1, u_2, u_3>> = U'
t0 := Cputime();
assert Subalgebra({@ u : u in us @}) eq VectorSpace(Up_alg);
Timed("subalgebra generated", t0);
print "Computation 5.5(b): <<u_1, u_2, u_3>> = U'.";
// (c) <<W'>> = U
t0 := Cputime();
assert Subalgebra({@ Ualg!Wp.i : i in [1..4] @}) eq VectorSpace(Ualg);
Timed("subalgebra generated", t0);
print "Computation 5.5(c): <<W'>> = U.";
// (d) the identity of U' extends to W' as a 1-dimensional space
t0 := Cputime();
bool, ext_Wp := ExtendAutToMod(Ualg, Up, Wp, IdentityMatrix(F, 7));
Timed("space of extensions to the module -> ext_Wp", t0);
assert bool and Dimension(ext_Wp) eq 1;
print "Computation 5.5(d): the extensions of id_{U'} to W' form a 1-dimensional space.";
// (e) (w^2, u) <> 0 for some nonzero w in W', u in U'
assert exists(wit){ <i, j> : i in [1..4], j in [1..7] |
   FrobeniusFormAtElements((Ualg!Wp.i)*(Ualg!Wp.i), Ualg!Up.j, form_U) ne 0 };
printf "Computation 5.5(e): (w^2, u) <> 0 for w = basis vector %o of W' and u = basis vector %o of U'.\n", wit[1], wit[2];

Section("Computation 5.7", t_start);
// u_i as elements of A
us_A := [A!((u@BasisMatrix(Up))@BasisMatrix(U)) : u in us];
assert forall{u : u in us_A | IsIdempotent(u)};
// (a) up to reordering, u_i has the eigenvalue 1/5 on W_i but not on W_j for j <> i
Ws := [W1, W2, W3];
has_fifth := [[ exists{e : e in Eigenvalues(RestrictMapToSubspace(AdMat(u), W)) | e[1] eq 1/5} : W in Ws] : u in us_A];
print "   u_i has eigenvalue 1/5 on W_j (rows i, columns j):", has_fifth;
assert forall{r : r in has_fifth | #[b : b in r | b] eq 1};
assert #{Index(r, true) : r in has_fifth} eq 3;
print "Computation 5.7(a): each u_i has the eigenvalue 1/5 on exactly one W_j, and these W_j are distinct.";
// (b) each W_i admits a 1-dimensional space of extensions of the identity of U
for k in [1..3] do
   t0 := Cputime();
   bool, ext_W := ExtendAutToMod(A, U, Ws[k], IdentityMatrix(F, 15));
   Timed("space of extensions to the module -> ext_W", t0);
   assert bool and Dimension(ext_W) eq 1;
   printf "Computation 5.7(b): the extensions of id_U to W_%o form a 1-dimensional space.\n", k;
end for;
// (c) <<W_1, W_2, W_3>> = A
t0 := Cputime();
assert Dimension(Subalgebra(&join[{@ A!W.i : i in [1..11] @} : W in Ws])) eq 76;
Timed("subalgebra generated", t0);
print "Computation 5.7(c): <<W_1, W_2, W_3>> = A.";
// (d) (w_i^2, u) <> 0 and (w_1 w_2, w_3) <> 0
w1 := A!W1.1;
w2 := A!W2.1;
w3 := A!W3.1;
assert exists(u){A!U.i : i in [1..15] |
   forall{wi : wi in [w1, w2, w3] | FrobeniusFormAtElements(wi*wi, A!U.i, form) ne 0}};
assert FrobeniusFormAtElements(w1*w2, w3, form) ne 0;
print "Computation 5.7(d): (w_i^2, u) <> 0 for i = 1, 2, 3 and (w_1 w_2, w_3) <> 0.";

Section("Done", t_start);
printf "Total CPU time: %o s\n", Cputime(t_start);
UnsetLogFile();
