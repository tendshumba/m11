// A_101.m  --  Section 6 of the revised paper: the 101-dimensional algebra for L_2(11)
//
// Rearranged (October 2026) to follow the computations of the revised paper, in order:
//   Computation 6.1  (a) no Jordan axes, (b) no twins, (c) involutions of G \ G_0 not induced by axes
//   Computation 6.2  joint eigenspace decomposition with respect to Y
//   (prose)          how x is found from b_1, b_2
//   Computation 6.3  (a) unique form on U, (b) x unique idempotent of length 20/7 [certificate, behind a flag],
//                    (c) spectrum of ad_x, (d) Seress law of x
//   Computation 6.4  (a) c_1, c_2 the only idempotents of length 176/35 in W = U_0(x), (b) W = <<c_1,c_2>>,
//                    (c) U = <<T>>, (d) H = End_W(T) two-dimensional, quadratic field with discriminant -3*square
//   Computation 6.5  (t_1^3, w) <> 0
//   Computation 6.7  (a) W_1, W_2, W_3 pairwise non-isomorphic U-modules, (b) <<W_1,W_2,W_3>> = A,
//                    (c) 1-dimensional extension spaces, (d) nonzero products
//
// Run from the directory containing Automorphisms.m, A_101, form_101:   magma A_101.m
// Output goes to A_101.log.
//
// certify_x := false skips the dimension/degree certificate for Computation 6.3(b): Groebner basis of the
// ideal of idempotents of length 20/7 in U (18 variables). This took 87,191 seconds (about a day) on a server
// running MAGMA V2.28-21; the full run (certify_x := true, the default) is the one archived in the repository.
// Everything else runs in minutes on a laptop.

certify_x := true;

SetSeed(1);
Attach("Automorphisms.m");
SetVerbose("Automorphisms", 0);
SetLogFile("A_101.log" : Overwrite := true);
t_start := Cputime();
Section := procedure(name, t0)
   printf "\n================ %o ================\n", name;
end procedure;
Timed := procedure(label, t0)
   printf "   [%o: %o s]\n", label, Cputime(t0);
end procedure;
F := Rationals();
// diagonalisability test for a rational matrix: the eigenspaces span the whole space
IsDiag := func< M | &+[Dimension(Eigenspace(M, e[1])) : e in Eigenvalues(M)] eq Nrows(M) >;

Section("Setup", t_start);
t0 := Cputime();
A_101 := eval Read("A_101");
Timed("reading the data file -> A_101", t0);
t0 := Cputime();
form_101 := eval Read("form_101");
Timed("reading the data file -> form_101", t0);
axes_101 := [A_101.i : i in [1..101] | IsIdempotent(A_101.i)];
assert #axes_101 eq 55;
t0 := Cputime();
Miy101_p, Miy101, isom101, gpname101 := MiyamotoGroup(axes_101);
Timed("Miyamoto group -> Miy101_p, Miy101, isom101, gpname101", t0);
t0 := Cputime();
G_perm, G, iso_G, gpname_G, _ := GroupFromAxes(axes_101);
Timed("group of automorphisms preserving the axet -> G_perm, G, iso_G, gpname_G, _", t0);
assert gpname_G eq "PSL(2,11).C2";
G0 := Miy101;

// The positive definite form form_101 is the one of the paper. Its uniqueness up to scale follows from
// Corollary 3.6 (no Jordan axes, Computation 6.1(a), and G_0 = L_2(11) simple); it is NOT a computation here.

// Sylow 2-subgroup S (dihedral of order 8), its involutions, the Klein four-group E and the axes Y
S := SylowSubgroup(G, 2);
assert GroupName(S) eq "D4" and Order(S) eq 8;
invs_S := [x : x in ConjugacyClasses(S) | x[1] eq 2];
assert #invs_S eq 3;
assert exists(cent){ x : x in invs_S | x[2] eq 1};
tau_1 := cent[3];
t0 := Cputime();
_, a1 := IsInducedFromAxis(A_101, Matrix(tau_1) : automorphism_check := false, form := form_101);
Timed("search for axes inducing the involution -> _, a1", t0);
a_1 := a1[1];
others := [x : x in invs_S | x ne cent];
for x in others do
   t := x[3];
   t0 := Cputime();
   bool, X := IsInducedFromAxis(A_101, Matrix(t) : automorphism_check := false, form := form_101);
   Timed("search for axes inducing the involution -> X", t0);
   if bool then
      tau_2 := t;
      assert #X eq 1;
      a_2 := X[1];
      Yv := Vector(a_2)^S;
      assert exists(a_3){ a : a in Yv | a ne a_2};
      a_3 := A_101!a_3;
   else
      printf "   (the class of size %o of involutions of S is not induced by axes)\n", x[2];
   end if;
end for;
Y := {@ a_1, a_2, a_3 @};
assert exists(tau_3){x : x in Class(S, tau_2) | x ne tau_2};
E := sub< S | tau_1, tau_2, tau_3 >;
assert GroupName(E) eq "C2^2";
N0 := Normaliser(G0, E);
assert GroupName(N0) eq "A4";
N := Normaliser(G, E);
assert GroupName(N) eq "S4";

Section("Computation 6.1", t_start);
// (a) no Jordan axes
t0 := Cputime();
jordans := JordanAxes(A_101, [Matrix(x) : x in Generators(Miy101)] : form := form_101);
Timed("search for Jordan axes -> jordans", t0);
assert IsEmpty(jordans);
print "Computation 6.1(a): A has no Jordan axes.";
// (b) no twins (one axis suffices, the axes form a single G_0-orbit)
t0 := Cputime();
twins := FindTwins(axes_101[1] : form := form_101);
Timed("search for twins -> twins", t0);
assert IsEmpty(twins);
print "Computation 6.1(b): the 55 axes have no twins.";
// (c) the involutions in G \ G_0 are not induced by axes
invs_G := [x : x in ConjugacyClasses(G) | x[1] eq 2];
assert #invs_G eq 2;
assert exists(c_2A){x : x in invs_G | x[3] in G0};
assert c_2A[2] eq 55;
assert exists(c_2B){x : x in invs_G | not x[3] in G0};
t0 := Cputime();
bool, _ := IsInducedFromAxis(A_101, Matrix(c_2B[3]) : form := form_101, automorphism_check := false);
Timed("search for axes inducing the involution -> _", t0);
assert not bool;
print "Computation 6.1(c): the involutions in G \\ G_0 are not induced by axes.";

Section("Computation 6.2", t_start);
t0 := Cputime();
decomps := JointEigenspaceDecomposition(Y);
Timed("joint eigenspace decomposition -> decomps", t0);
assert Keys(decomps) eq {[0,0,0], [1/4,1/32,1/32], [1/32,1/4,1/32], [1/32,1/32,1/4],
                         [0,1/32,1/32], [1/32,0,1/32], [1/32,1/32,0]};
U := decomps[[0,0,0]];
assert Dimension(U) eq 18;
assert forall{x : x in [[1/4,1/32,1/32], [1/32,1/4,1/32], [1/32,1/32,1/4]] | Dimension(decomps[x]) eq 5};
assert forall{x : x in [[0,1/32,1/32], [1/32,0,1/32], [1/32,1/32,0]] | Dimension(decomps[x]) eq 17};
W1 := decomps[[0, 1/32, 1/32]];
W2 := decomps[[1/32, 0, 1/32]];
W3 := decomps[[1/32, 1/32, 0]];
print "Computation 6.2: dim U = 18; the 1/4-components have dimension 5; W_1, W_2, W_3 have dimension 17.";

Section("Finding x (prose before Computation 6.3)", t_start);
// V = <<Y>> is a 2B-type subalgebra with identity 1_V = 4/5 (a_1+a_2+a_3).
t0 := Cputime();
V := Subalgebra(Y);
Timed("subalgebra generated -> V", t0);
assert Dimension(V) eq 3;
one_V := 4/5*(&+Y);
assert forall{y : y in Y | one_V*y eq y};
// B_1, B_2: the subalgebras for the two classes of A_5 in G_0 containing N_0 (dimension 26 each);
// b_i := 1_{B_i} - 1_V are idempotents of U of length 276/35.
subs_60 := Subgroups(G0 : OrderEqual := 60);
assert #subs_60 eq 2 and forall{x : x in subs_60 | GroupName(x`subgroup) eq "A5"};
H1 := subs_60[1]`subgroup;
H2 := subs_60[2]`subgroup;
assert exists(g1){g : g in G0 | N0 subset H1^g};
assert exists(g2){g : g in G0 | N0 subset H2^g};
H1 := H1^g1;
H2 := H2^g2;
B1 := SubalgebraCorrespondingToSubgroup(A_101, H1 : axes := axes_101, Miyamoto_group := G0);
B2 := SubalgebraCorrespondingToSubgroup(A_101, H2 : axes := axes_101, Miyamoto_group := G0);
assert Dimension(B1) eq 26 and Dimension(B2) eq 26;
t0 := Cputime();
B1_alg := Algebra< F, 26 | AllStructureConstants(FindStructureConstantsSubalgebra(A_101, B1)) >;
Timed("structure constants of the subalgebra -> B1_alg", t0);
t0 := Cputime();
B2_alg := Algebra< F, 26 | AllStructureConstants(FindStructureConstantsSubalgebra(A_101, B2)) >;
Timed("structure constants of the subalgebra -> B2_alg", t0);
_, one_B1 := HasOne(B1_alg);
_, one_B2 := HasOne(B2_alg);
one_B1b := A_101!(one_B1@BasisMatrix(B1));
one_B2b := A_101!(one_B2@BasisMatrix(B2));
assert forall{i : i in [1..26] | one_B1b*(A_101!B1.i) eq B1.i};
assert forall{i : i in [1..26] | one_B2b*(A_101!B2.i) eq B2.i};
b1 := one_B1b - one_V;
b2 := one_B2b - one_V;
assert b1 in U and b2 in U;
// U as an algebra in its own right, with the restricted form
t0 := Cputime();
Ualg := Algebra< F, 18 | AllStructureConstants(FindStructureConstantsSubalgebra(A_101, U)) >;
Timed("structure constants of the subalgebra -> Ualg", t0);
form_U := RestrictedForm(form_101, U);
b1_s := Ualg!(b1@@BasisMatrix(U));
b2_s := Ualg!(b2@@BasisMatrix(U));
assert IsIdempotent(b1_s) and IsIdempotent(b2_s);
assert LengthOfElement(b1_s, form_U) eq 276/35 and LengthOfElement(b2_s, form_U) eq 276/35;
// W' := U_1(b_1) meet U_1(b_2) is 1-dimensional and contains a unique nonzero idempotent x, of length 20/7
U_1b1 := Eigenspace(AdMat(b1), 1)@@BasisMatrix(U);
U_1b2 := Eigenspace(AdMat(b2), 1)@@BasisMatrix(U);
assert Dimension(U_1b1) eq 4 and Dimension(U_1b2) eq 4;
W_p := U_1b1 meet U_1b2;
assert Dimension(W_p) eq 1;
t0 := Cputime();
idempsW_p := FindAllIdempotents(Ualg, W_p);
Timed("idempotent search (Groebner basis) -> idempsW_p", t0);
assert #idempsW_p eq 2;
assert exists(x){x : x in idempsW_p | x ne 0};
assert LengthOfElement(x, form_U) eq 20/7;
print "x found: the nonzero idempotent in U_1(b_1) meet U_1(b_2), of length 20/7.";

Section("Computation 6.3", t_start);
// (a) U admits a unique Frobenius form up to scale
t0 := Cputime();
bool, forms_U := HasFrobeniusForm(Ualg);
Timed("space of Frobenius forms -> forms_U", t0);
assert bool and Dimension(forms_U) eq 1;
print "Computation 6.3(a): the space of Frobenius forms on U is 1-dimensional.";
// (b) x is the unique idempotent of length 20/7 in U over the algebraic closure (certificate)
if certify_x then
   print "Computation 6.3(b): certificate (Groebner basis of the ideal of idempotents of length 20/7 in U).";
   I := GetIdempotentIdeal(Ualg, VectorSpace(Ualg) : length := 20/7, form := form_U, subalgebra := true);
   printf "Ideal in %o variables with %o generators.\n", Rank(Generic(I)), #Basis(I);
   assert forall{f : f in Basis(I) | Evaluate(f, Eltseq(x)) eq 0};
   t0 := Cputime();
   Groebner(I);
   printf "Groebner basis computed in %o seconds.\n", Cputime(t0);
   d := Dimension(I);
   printf "Krull dimension of the ideal: %o\n", d;
   assert d eq 0;
   deg := QuotientDimension(I);
   printf "Degree of the ideal (dimension of the quotient): %o\n", deg;
   assert deg eq 1;
   print "Computation 6.3(b): x is the unique idempotent of length 20/7 in U over the algebraic closure.";
else
   print "Computation 6.3(b): certificate skipped (set certify_x := true to run it; about a day on a server).";
end if;
// (c) spectrum of ad_x on U
ad_x := AdMat(x);
assert IsDiag(ad_x);
assert Eigenvalues(ad_x) eq {<1,1>, <0,5>, <1/14,6>, <2/7,2>, <3/7,4>};
print "Computation 6.3(c): ad_x is diagonalisable on U with eigenvalues 1, 0, 1/14, 2/7, 3/7 of multiplicities 1, 5, 6, 2, 4.";
// (d) x satisfies an ungraded Seress fusion law on U
t0 := Cputime();
fus_law := FindFusionLaw(x);
Timed("fusion law of the idempotent -> fus_law", t0);
print "Fusion law of x on U:", fus_law;
assert exists{ i : i in [1..#fus_law] | fus_law[i] eq [* <0, 1/14>, [1/14] *] };
assert exists{ i : i in [1..#fus_law] | fus_law[i] eq [* <0, 2/7>, [2/7] *] };
assert exists{ i : i in [1..#fus_law] | fus_law[i] eq [* <0, 3/7>, [3/7] *] };
print "Computation 6.3(d): 0 * lambda is contained in {lambda} for every eigenvalue lambda, so the law is Seress.";

Section("W = U_0(x), c_1, c_2, T, H", t_start);
W := Eigenspace(ad_x, 0);
assert Dimension(W) eq 5;
c1 := b1_s - x;
c2 := b2_s - x;
assert IsIdempotent(c1) and IsIdempotent(c2);
assert c1 in W and c2 in W;
assert LengthOfElement(c1, form_U) eq 176/35 and LengthOfElement(c2, form_U) eq 176/35;
T := Eigenspace(ad_x, 1/14);
assert Dimension(T) eq 6;

Section("Computation 6.4", t_start);
// (a) c_1 and c_2 are the only idempotents of length 176/35 in W over the algebraic closure
t0 := Cputime();
idemps_W := FindAllIdempotents(Ualg, W : length := 176/35, form := form_U);
Timed("idempotent search (Groebner basis) -> idemps_W", t0);
assert Type(idemps_W) ne MonStgElt;                 // the ideal is zero-dimensional
assert #idemps_W eq 2;                              // two solutions over the algebraic closure ...
assert forall{y : y in idemps_W | IsCoercible(Ualg, y)};   // ... both rational ...
assert {Ualg!y : y in idemps_W} eq {c1, c2};        // ... namely c_1 and c_2
print "Computation 6.4(a): c_1, c_2 are the only idempotents of length 176/35 in W (over the algebraic closure).";
// (b) W = <<c_1, c_2>>
t0 := Cputime();
assert Subalgebra({@ c1, c2 @}) eq W;
Timed("subalgebra generated", t0);
print "Computation 6.4(b): W = <<c_1, c_2>>.";
// (c) U = <<T>>
t0 := Cputime();
assert Subalgebra({@ Ualg!T.i : i in [1..6] @}) eq VectorSpace(Ualg);
Timed("subalgebra generated", t0);
print "Computation 6.4(c): U = <<T>>.";
// (d) H = End_W(T): the W-module endomorphisms of T = extensions of the identity of W to T
t0 := Cputime();
bool, H := ExtendAutToMod(Ualg, W, T, IdentityMatrix(F, 5));
Timed("space of extensions to the module -> H", t0);
assert bool;
assert Dimension(H) eq 2;
Hmat := [Matrix(F, 6, 6, Eltseq(H.i)) : i in [1..2]];
// pick phi in H outside Q*id_T (any such phi will do; we take the first basis vector that is not scalar)
assert exists(phi){m : m in Hmat | not IsScalar(m)};
min_pol := MinimalPolynomial(phi);
assert Degree(min_pol) eq 2 and IsIrreducible(min_pol);
Dis := Discriminant(min_pol);
is_sq, r := IsSquare(-Dis/3);
assert is_sq;
printf "Computation 6.4(d): dim H = 2; minimal polynomial of phi: %o, discriminant %o = -3 * (%o)^2.\n", min_pol, Dis, r;
// (consistency check, not part of the paper: H is closed under composition, i.e. it is an algebra)
assert IsConsistent(Matrix(F, [Eltseq(H.1), Eltseq(H.2)]), Vector(Eltseq(phi^2)));

Section("T_1, T_2 over K = Q(sqrt(-3))", t_start);
// T_i are the simultaneous eigenspaces of H on T tensor K; since H = Q id + Q phi, they are the eigenspaces of phi.
K := CyclotomicField(3);                             // = Q(sqrt(-3))
roots := Roots(ChangeRing(min_pol, K));
assert #roots eq 2;
TK := ChangeRing(T, K);
phi_K := ChangeRing(phi, K);
T1 := EigenspaceOfMap(phi_K, TK, roots[1][1]);
T2 := EigenspaceOfMap(phi_K, TK, roots[2][1]);
assert Dimension(T1) eq 3 and Dimension(T2) eq 3;
UK := ChangeRing(Ualg, K);
WK := ChangeRing(W, K);
// T_1, T_2 are W-submodules (consequence of phi commuting with W; checked for safety)
assert forall{v : v in Basis(T1) | forall{w : w in Basis(WK) | (UK!v)*(UK!w) in T1}};
assert forall{v : v in Basis(T2) | forall{w : w in Basis(WK) | (UK!v)*(UK!w) in T2}};

Section("Computation 6.5", t_start);
// (t_1^3, w) <> 0 for some t_1 in T_1 and w in W (we take basis vectors; any witness suffices)
assert exists(wit){ <i, j> : i in [1..3], j in [1..5] |
   FrobeniusFormAtElements((UK!T1.i)*(UK!T1.i)*(UK!T1.i), UK!WK.j, form_U) ne 0 };
t1 := UK!T1.(wit[1]);
w := UK!WK.(wit[2]);
printf "Computation 6.5: (t_1^3, w) <> 0 for t_1 = basis vector %o of T_1 and w = basis vector %o of W (the value is a nonzero element of K).\n", wit[1], wit[2];

Section("Computation 6.7", t_start);
// (a) the U-modules W_1, W_2, W_3 are pairwise non-isomorphic: an element u of U whose characteristic
//     polynomials on W_1, W_2, W_3 are pairwise different certifies this. We try, deterministically, x, b_1, b_2
//     and then the basis vectors of U, and record the first witness.
ActionOn := function(u, M)
   BM := BasisMatrix(M);
   return Matrix([Solution(BM, Vector(u*(A_101!M.i))) : i in [1..Dimension(M)]]);
end function;
ToA := function(y) return A_101!(Vector(y)*BasisMatrix(U)); end function;
candidates := [<"x", ToA(x)>, <"b_1", b1>, <"b_2", b2>] cat [<"U." cat IntegerToString(i), A_101!U.i> : i in [1..18]];
assert exists(cand){c : c in candidates |
   #{CharacteristicPolynomial(ActionOn(c[2], M)) : M in [W1, W2, W3]} eq 3};
printf "Computation 6.7(a): the characteristic polynomials of ad_u on W_1, W_2, W_3 are pairwise different for u = %o\n", cand[1];
printf "   (degrees of the irreducible factors, with multiplicities, on W_1, W_2, W_3: %o)\n",
   [[<Degree(f[1]), f[2]> : f in Factorisation(CharacteristicPolynomial(ActionOn(cand[2], M)))] : M in [W1, W2, W3]];
print "   so W_1, W_2, W_3 are pairwise non-isomorphic U-modules.";
// (b) <<W_1, W_2, W_3>> = A
t0 := Cputime();
assert Dimension(Subalgebra(&join[{@ A_101!M.i : i in [1..Dimension(M)] @} : M in [W1, W2, W3]])) eq 101;
Timed("subalgebra generated", t0);
print "Computation 6.7(b): <<W_1, W_2, W_3>> = A.";
// (c) each W_i admits a 1-dimensional space of extensions of the identity of U
for M in [<"W_1", W1>, <"W_2", W2>, <"W_3", W3>] do
   t0 := Cputime();
   bool, ext := ExtendAutToMod(A_101, U, M[2], IdentityMatrix(F, 18));
   Timed("space of extensions to the module -> ext", t0);
   assert bool and Dimension(ext) eq 1;
   printf "Computation 6.7(c): the extensions of id_U to %o form a 1-dimensional space.\n", M[1];
end for;
// (d) (w_i^2, u) <> 0 and (w_1 w_2, w_3) <> 0 for some w_i in W_i, u in U
w1 := A_101!W1.1;
w2 := A_101!W2.1;
w3 := A_101!W3.1;
assert exists(u){A_101!U.i : i in [1..18] |
   forall{wi : wi in [w1, w2, w3] | FrobeniusFormAtElements(wi*wi, A_101!U.i, form_101) ne 0}};
assert FrobeniusFormAtElements(w1*w2, w3, form_101) ne 0;
print "Computation 6.7(d): (w_i^2, u) <> 0 for i = 1, 2, 3 and (w_1 w_2, w_3) <> 0 (first basis vectors of W_i, a basis vector u of U).";

Section("Done", t_start);
printf "Total CPU time: %o s\n", Cputime(t_start);
UnsetLogFile();
