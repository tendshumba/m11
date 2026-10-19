// A_286.m  --  Section 7 of the revised paper: the 286-dimensional algebra for M_11
//
// Rearranged (October 2026) to follow the computations of the revised paper, in order:
//   Computation 7.1  (a) eigenspace dimensions of ad_a, (b) no Jordan axes, (c) no twins
//   (setup)          S, P, the axes a, a_1..a_4, the 4B-subalgebra F, e, u = e - a, U = A_0(a), v, w
//   Computation 7.2  (a) spectrum of ad_u on U, (b) spectra of ad_v, ad_w on U, (c) v, w axes of type AM(3/10,1/20)
//   (prose)          D = U_1(u) has exactly four idempotents; T = U_{7/20}(e) = T_1 + T_2
//   Computation 7.3  J = U_0(u), J_0, B, L: (a) dimensions, (b) projections of squares from L generate J_0,
//                    (c) unique idempotents of lengths 26/5 and 36/5 generate J_0, (d) extensions of id_{J_0} to B,
//                    (e) b in B with (b^2) having nonzero projection to J_0
//   Computation 7.5  (a) <<T>> = U, (b) extensions of id_J to T_i, (c) extensions of rho to T_i,
//                    (d) (t_i^2, b) <> 0 and the ratio c_i^2, (e) none of the four candidate maps extends to Aut(U)
//   Computation 7.7  K = A_{1/32}(a): (a) <<K>> = A, (b) extensions of id_U to K, (c) (k^2, u_0) <> 0
//   Remark (exactness) elements of S \ P induce rho on J; tau_v = z_3|_U, tau_w = z_1|_U
//   Computation 7.11 (modular data) is in the separate scripts Lemma_6_27.m / IsSixTranspositionClass.m.
//
// Naming follows the paper: the 4B-subalgebra is F4B (the letter F is the base field in MAGMA), the
// 4-dimensional complement of J in A_0(u) is L, and K is A_{1/32}(a).
//
// Random seed policy (18 October 2026). The seed is NOT set by this script. The running time of some package
// routines depends strongly on MAGMA's random choices (with SetSeed(1) the generic extension routine did not
// finish Computation 7.7(b) in 24 hours), so instead the state of the random generator (seed and step) is
// printed at the start and before every package call. Any individual step can be reproduced exactly by
// inserting SetSeed(seed, step) with the printed values before that call, and the whole run by
//    magma -S<seed> A_286.m
// with the seed printed at the start.
//
// Computation 7.7(b) is done by a deterministic method of its own (no random choices, no system in 132^2
// unknowns): the extensions of id_U to K are the U-module endomorphisms of K, which are contained in the
// commutant of ad_{u_j}|_K for any fixed elements u_j of U; that commutant is computed by the cyclic-vector
// method with 132 unknowns. See the comments in the section "Computation 7.7".
//
// Run from the directory containing Automorphisms.m, A_286, form_286:   magma A_286.m
// Output goes to A_286.log. The slowest steps: the setup (fusion law check, Miyamoto group, twins: about
// 20 minutes in total) and the subalgebra generation check <<K>> = A in 7.7(a) (about 30 minutes).

Attach("Automorphisms.m");
SetVerbose("Automorphisms", 0);
SetVerbose("Fusion_check", 0);
SetLogFile("A_286.log" : Overwrite := true);
t_start := Cputime();
Section := procedure(name, t0)
   printf "\n================ %o ================\n", name;
end procedure;
// Begin: print the state of the random generator before a (possibly randomised) package call, return the start time
Begin := function(label)
   s, c := GetSeed();
   printf "   [%o: start; seed = %o, step = %o]\n", label, s, c;
   return Cputime();
end function;
Timed := procedure(label, t0)
   printf "   [%o: %o s]\n", label, Cputime(t0);
end procedure;
F := Rationals();
// diagonalisability test for a rational matrix: the eigenspaces span the whole space
IsDiag := func< M | &+[Dimension(Eigenspace(M, e[1])) : e in Eigenvalues(M)] eq Nrows(M) >;

Section("Setup", t_start);
s0, c0 := GetSeed();
printf "MAGMA random seed at start: seed = %o, step = %o (reproduce the run with  magma -S%o A_286.m  or SetSeed(%o, %o)).\n", s0, c0, s0, s0, c0;
t0 := Begin("reading the data file -> A");
A := eval Read("A_286");
Timed("reading the data file -> A", t0);
t0 := Begin("reading the data file -> form");
form := eval Read("form_286");
Timed("reading the data file -> form", t0);
axes := [A.i : i in [1..286] | IsIdempotent(A.i)];
assert #axes eq 165;
t0 := Begin("Monster fusion law check");
assert HasMonsterFusionLaw(axes[1]);
Timed("Monster fusion law check", t0);
t0 := Begin("Miyamoto group -> G_p, G, isom, gpname");
G_p, G, isom, gpname := MiyamotoGroup(axes);
Timed("Miyamoto group -> G_p, G, isom, gpname", t0);
print "Miyamoto group:", gpname;
// The form form_286 is the positive definite Frobenius form of the paper; its uniqueness up to scale follows from
// Corollary 3.6 (no Jordan axes, Computation 7.1(b), and M_11 simple), not from a computation.

Section("Computation 7.1", t_start);
// (a) eigenspace dimensions of ad_a for an axis a
ad_a0 := AdMat(axes[1]);
assert IsDiag(ad_a0);
assert Eigenvalues(ad_a0) eq {<1,1>, <0,128>, <1/4,25>, <1/32,132>};
print "Computation 7.1(a): the 1-, 0-, 1/4-, 1/32-eigenspaces of ad_a have dimensions 1, 128, 25, 132.";
// (b) no Jordan axes
t0 := Begin("search for Jordan axes -> jordans");
jordans := JordanAxes(A, [Matrix(g) : g in Generators(G)] : form := form);
Timed("search for Jordan axes -> jordans", t0);
assert IsEmpty(jordans);
print "Computation 7.1(b): A has no Jordan axes.";
// (c) no twins
t0 := Begin("search for twins -> twins");
twins := FindTwins(axes[1] : form := form);
Timed("search for twins -> twins", t0);
assert IsEmpty(twins);
print "Computation 7.1(c): the 165 axes have no twins.";

Section("Setup: S, P, a, a_1, ..., a_4, F4B, e, u, U, v, w", t_start);
S := SylowSubgroup(G_p, 2)@isom;
assert Order(S) eq 16;
invs_S := [x : x in ConjugacyClasses(S) | x[1] eq 2];
assert #invs_S eq 2;
assert exists(cent_class){x : x in invs_S | x[2] eq 1};
z := cent_class[3];
assert exists(other){x : x in invs_S | x[2] ne 1};
C := Class(S, other[3]);
assert #C eq 4;
P := sub< S | C join {z} >;
assert Order(P) eq 8;
invs_P := [x : x in ConjugacyClasses(P) | x[1] eq 2];
assert #invs_P eq 3;
twos := [x : x in invs_P | x[2] ne 1];
assert #twos eq 2 and &join[x[3]^P : x in twos] eq C;
assert P eq sub< P | [x[3] : x in twos] >;
// axes corresponding to z and to the two P-classes {z_1,z_2}, {z_3,z_4} in C
t0 := Begin("Miyamoto involutions of all axes -> taus");
taus := [TauMapMonster(axes[i]) : i in [1..165]];
Timed("Miyamoto involutions of all axes -> taus", t0);
a := axes[Index(taus, Matrix(z))];
assert TauMapMonster(a) eq z;
z1 := twos[1][3];
assert exists(g){g : g in P | z1^g ne z1};
z2 := (P!z1)^g;
z3 := twos[2][3];
assert exists(g){g : g in P | z3^g ne z3};
z4 := (P!z3)^g;
a1 := axes[Index(taus, Matrix(z1))];
a2 := axes[Index(taus, Matrix(z2))];
a3 := axes[Index(taus, Matrix(z3))];
a4 := axes[Index(taus, Matrix(z4))];
assert forall{p : p in [<a1,z1>, <a2,z2>, <a3,z3>, <a4,z4>] | TauMapMonster(p[1]) eq Matrix(p[2])};
// F4B = <<a_1, a_3>> is of type 4B, 5-dimensional, with basis {a, a_1, a_2, a_3, a_4}
t0 := Begin("subalgebra generated -> F4B");
F4B := Subalgebra({@ a1, a3 @});
Timed("subalgebra generated -> F4B", t0);
assert Dimension(F4B) eq 5;
assert a1*a3 eq 1/64*(a1 + a3 - a2 - a4 + a);
assert forall{x : x in [a, a1, a2, a3, a4] | Vector(x) in F4B};
// identity e of F4B, u := e - a in U := A_0(a)
e := 4/5*(a1 + a2 + a3 + a4) + 3/5*a;
assert IsIdempotent(e);
assert forall{x : x in [a, a1, a2, a3, a4] | x*e eq x};
ad_a := AdMat(a);
U := Eigenspace(ad_a, 0);
assert Dimension(U) eq 128;
t0 := Begin("structure constants of the subalgebra -> Ualg");
Ualg := Algebra< F, 128 | AllStructureConstants(FindStructureConstantsSubalgebra(A, U)) >;
Timed("structure constants of the subalgebra -> Ualg", t0);
form_U := RestrictedForm(form, U);
u := e - a;
assert u in U;
u_s := Ualg!(u@@BasisMatrix(U));
assert IsIdempotent(u_s);
// V = <a, a_1, a_2>, W = <a, a_3, a_4> are the two 2A-subalgebras; v := e - 1_V, w := e - 1_W
one_V := 4/5*(a + a1 + a2);
one_W := 4/5*(a + a3 + a4);
assert forall{x : x in [a, a1, a2] | x*one_V eq x};
assert forall{x : x in [a, a3, a4] | x*one_W eq x};
v := e - one_V;
w := e - one_W;
v_s := Ualg!(v@@BasisMatrix(U));
w_s := Ualg!(w@@BasisMatrix(U));
assert IsIdempotent(v_s) and IsIdempotent(w_s);
assert v*w eq 0;
assert LengthOfElement(v_s, form_U) eq 7/5 and LengthOfElement(w_s, form_U) eq 7/5;
assert LengthOfElement(u_s, form_U) eq 14/5;
print "Setup done: v, w idempotents of length 7/5 with vw = 0; u = v + w of length 14/5.";

Section("Computation 7.2", t_start);
ad_eU := RestrictMapToSubspace(AdMat(e), U);
ad_uU := AdMat(u_s);
assert ad_eU eq ad_uU;
// (a)
assert IsDiag(ad_uU);
assert Eigenvalues(ad_uU) eq {<1,2>, <0,26>, <3/10,14>, <7/20,12>, <1/20,50>, <1/10,24>};
D := Eigenspace(ad_uU, 1);
J := Eigenspace(ad_uU, 0);
assert Dimension(D) eq 2 and Dimension(J) eq 26;
t0 := Begin("subalgebra test for D and J");
assert IsSubalgebra(Ualg, D) and IsSubalgebra(Ualg, J);
Timed("subalgebra test for D and J", t0);
print "Computation 7.2(a): ad_u|_U diagonalisable, eigenvalues 1, 0, 3/10, 7/20, 1/20, 1/10 of multiplicities 2, 26, 14, 12, 50, 24.";
// (b)
ad_vU := AdMat(v_s);
ad_wU := AdMat(w_s);
assert IsDiag(ad_vU) and IsDiag(ad_wU);   // stated in 7.2(b); the fusion law check in (c) implies it again
assert Eigenvalues(ad_vU) eq {<1,1>, <0,59>, <3/10,13>, <1/20,55>};
assert Eigenvalues(ad_wU) eq {<1,1>, <0,59>, <3/10,13>, <1/20,55>};
print "Computation 7.2(b): ad_v|_U and ad_w|_U diagonalisable, eigenvalues 1, 0, 3/10, 1/20 of multiplicities 1, 59, 13, 55.";
// (c)
t0 := Begin("fusion law check for v");
assert HasAlmostMonsterFusionLaw(v_s : arbitrary_parameters := <3/10, 1/20>);
Timed("fusion law check for v", t0);
t0 := Begin("fusion law check for w");
assert HasAlmostMonsterFusionLaw(w_s : arbitrary_parameters := <3/10, 1/20>);
Timed("fusion law check for w", t0);
print "Computation 7.2(c): v and w are primitive axes of U of almost Monster type (3/10, 1/20).";

Section("Prose after Computation 7.2: idempotents of D, T = T_1 + T_2", t_start);
assert v_s in D and w_s in D;
t0 := Begin("idempotent search (Groebner basis) -> idemps_D");
idemps_D := FindAllIdempotents(Ualg, D);
Timed("idempotent search (Groebner basis) -> idemps_D", t0);
assert #idemps_D eq 4;
assert {Ualg!y : y in idemps_D} eq {Ualg!0, v_s, w_s, u_s};
print "D = U_1(u) contains exactly the four idempotents 0, v, w, u.";
T := Eigenspace(ad_uU, 7/20);
assert Dimension(T) eq 12;
T1 := Eigenspace(ad_vU, 3/10) meet Eigenspace(ad_wU, 1/20);
T2 := Eigenspace(ad_vU, 1/20) meet Eigenspace(ad_wU, 3/10);
assert Dimension(T1) eq 6 and Dimension(T2) eq 6;
assert T1 + T2 eq T;
print "T = U_{7/20}(e) = T_1 + T_2 with T_1 = U_{3/10}(v) meet U_{1/20}(w), T_2 = U_{1/20}(v) meet U_{3/10}(w), both 6-dimensional.";

Section("Computation 7.3", t_start);
t0 := Begin("structure constants of the subalgebra -> Jalg");
Jalg := Algebra< F, 26 | AllStructureConstants(FindStructureConstantsSubalgebra(Ualg, J)) >;
Timed("structure constants of the subalgebra -> Jalg", t0);
Jb := J@BasisMatrix(U);                 // J as a subspace of A
form_J := RestrictedForm(form, Jb);
// J_0 := fixed points of S on J (S acts on J since it fixes a and e)
gensS := SetToSequence(Generators(S));
gensS_J := [m : m in {@ RestrictMapToSubspace(Matrix(g), Jb) : g in gensS @} | not IsIdentity(m)];
t0 := Begin("fixed subalgebra -> J0");
J0 := FindFixedSubalgebra(Jalg, gensS_J);
Timed("fixed subalgebra -> J0", t0);
assert forall{m : m in gensS_J | forall{i : i in [1..Dimension(J0)] | J0.i*m eq J0.i}};
// (a)
assert Dimension(J0) eq 14;
t0 := Begin("orthogonal complement -> B");
B := FindPerpWithRespectToForm(Jalg, VectorSpace(Jalg), J0 : form := form_J);
Timed("orthogonal complement -> B", t0);
assert Dimension(B) eq 12;
assert forall{i : i in [1..14] | forall{j : j in [1..12] | FrobeniusFormAtElements(Jalg!J0.i, Jalg!B.j, form_J) eq 0}};
assert forall{i : i in [1..12] | forall{j : j in [1..14] | (Jalg!B.i)*(Jalg!J0.j) in B}};   // B is a J_0-module (Lemma 3.2)
print "Computation 7.3(a): dim J_0 = 14, dim B = 12.";
// (b) A_0(u) has dimension 30; L, the orthogonal complement of J in A_0(u), is 4-dimensional,
//     and the projections to J of the squares of the elements of L generate J_0 as a subalgebra
t0 := Begin("eigenspace computation -> A0_u");
A0_u := Eigenspace(AdMat(u), 0);
Timed("eigenspace computation -> A0_u", t0);
assert Dimension(A0_u) eq 30;
assert Jb subset A0_u;
t0 := Begin("orthogonal complement -> L");
L := FindPerpWithRespectToForm(A, A0_u, Jb : form := form);
Timed("orthogonal complement -> L", t0);
assert Dimension(L) eq 4;
assert forall{i : i in [1..4] | forall{j : j in [1..26] | FrobeniusFormAtElements(A!Jb.j, A!L.i, form) eq 0}};
ProjJb := ProjectionToSubspace(A, Jb, form);
squares_L_proj := {@ ((A!L.i)*(A!L.i))*ProjJb : i in [1..4] @};
assert forall{y : y in squares_L_proj | y in Jb};
J0b := (J0@BasisMatrix(J))@BasisMatrix(U);      // J_0 as a subspace of A
// the projections generate J_0 as a subalgebra (they cannot span it: dim J_0 = 14 > 10 = dim Sym^2(L))
t0 := Begin("subalgebra generated by the projected squares");
assert Subalgebra({@ Ualg!(y@@BasisMatrix(U)) : y in squares_L_proj @}) eq J0@BasisMatrix(J);
Timed("subalgebra generated by the projected squares", t0);
print "Computation 7.3(b): dim A_0(u) = 30, dim L = 4; the projections to J of the squares of the elements of L generate J_0 as a subalgebra.";
// (c) over the algebraic closure, J_0 contains a unique idempotent of length 26/5 and a unique one of length 36/5;
//     both are rational and generate J_0
t0 := Begin("structure constants of the subalgebra -> J0alg");
J0alg := Algebra< F, 14 | AllStructureConstants(FindStructureConstantsSubalgebra(Jalg, J0)) >;
Timed("structure constants of the subalgebra -> J0alg", t0);
form_J0 := RestrictedForm(form, J0b);
t0 := Begin("idempotent search (Groebner basis) -> idemps_26_5");
idemps_26_5 := FindAllIdempotents(J0alg, VectorSpace(J0alg) : length := 26/5, form := form_J0);
Timed("idempotent search (Groebner basis) -> idemps_26_5", t0);
assert Type(idemps_26_5) ne MonStgElt and #idemps_26_5 eq 1 and IsCoercible(J0alg, idemps_26_5[1]);
t0 := Begin("idempotent search (Groebner basis) -> idemps_36_5");
idemps_36_5 := FindAllIdempotents(J0alg, VectorSpace(J0alg) : length := 36/5, form := form_J0);
Timed("idempotent search (Groebner basis) -> idemps_36_5", t0);
assert Type(idemps_36_5) ne MonStgElt and #idemps_36_5 eq 1 and IsCoercible(J0alg, idemps_36_5[1]);
j1 := J0alg!idemps_26_5[1];
j2 := J0alg!idemps_36_5[1];
t0 := Begin("subalgebra generated by j_1, j_2");
assert Subalgebra({@ j1, j2 @}) eq VectorSpace(J0alg);
Timed("subalgebra generated by j_1, j_2", t0);
print "Computation 7.3(c): unique idempotents j_1, j_2 of lengths 26/5 and 36/5 in J_0 (over the algebraic closure), rational, with <<j_1, j_2>> = J_0.";
// (d) the extensions of id_{J_0} to B form a 1-dimensional space (the scalars)
t0 := Begin("space of extensions to the module -> ext_J0_B");
bool, ext_J0_B := ExtendAutToMod(Jalg, J0, B, IdentityMatrix(F, 14));
Timed("space of extensions to the module -> ext_J0_B", t0);
assert bool and Dimension(ext_J0_B) eq 1;
assert IsScalar(Matrix(F, 12, 12, Eltseq(ext_J0_B.1)));
print "Computation 7.3(d): the extensions of id_{J_0} to B form a 1-dimensional space, consisting of the scalar maps.";
// (e) some b in B has (b^2) with nonzero projection to J_0
ProjJ0 := ProjectionToSubspace(Jalg, J0, form_J);
assert exists(ib){ i : i in [1..12] | ((Jalg!B.i)*(Jalg!B.i))*ProjJ0 ne 0 };
printf "Computation 7.3(e): for b = basis vector %o of B, the projection of b^2 to J_0 is nonzero.\n", ib;

Section("rho", t_start);
// rho: the linear map of J which is the identity on J_0 and -1 on B (matrix in the basis of J, row convention)
Mchange := VerticalJoin(BasisMatrix(J0), BasisMatrix(B));
assert Nrows(Mchange) eq 26 and Rank(Mchange) eq 26;
rho := Mchange^-1 * DiagonalMatrix(F, [1 : i in [1..14]] cat [-1 : i in [1..12]]) * Mchange;
assert forall{i : i in [1..14] | J0.i*rho eq J0.i};
assert forall{i : i in [1..12] | B.i*rho eq -B.i};
assert rho^2 eq IdentityMatrix(F, 26);

Section("Computation 7.5", t_start);
// (a) <<T>> = U
t0 := Begin("subalgebra generated by T");
assert Subalgebra({@ Ualg!T.i : i in [1..12] @}) eq VectorSpace(Ualg);
Timed("subalgebra generated by T", t0);
print "Computation 7.5(a): <<T>> = U.";
// (b) the extensions of id_J to T_i form a 1-dimensional space spanned by id_{T_i}
for pair in [<"T_1", T1>, <"T_2", T2>] do
   t0 := Begin("space of extensions of id_J to " cat pair[1] cat " -> ext");
   bool, ext := ExtendAutToMod(Ualg, J, pair[2], IdentityMatrix(F, 26));
   Timed("space of extensions of id_J to " cat pair[1] cat " -> ext", t0);
   assert bool and Dimension(ext) eq 1;
   assert IsIdentity(Matrix(F, 6, 6, Eltseq(ext.1)));
   printf "Computation 7.5(b): the extensions of id_J to %o form a 1-dimensional space, spanned by the identity.\n", pair[1];
end for;
// (c) the extensions of rho to T_i form a 1-dimensional space, spanned by phi_i
t0 := Begin("space of extensions of rho to T_1 -> ext_rho_T1");
bool, ext_rho_T1 := ExtendAutToMod(Ualg, J, T1, rho);
Timed("space of extensions of rho to T_1 -> ext_rho_T1", t0);
assert bool and Dimension(ext_rho_T1) eq 1;
t0 := Begin("space of extensions of rho to T_2 -> ext_rho_T2");
bool, ext_rho_T2 := ExtendAutToMod(Ualg, J, T2, rho);
Timed("space of extensions of rho to T_2 -> ext_rho_T2", t0);
assert bool and Dimension(ext_rho_T2) eq 1;
phi_1 := MapFromMatrix(Matrix(F, 6, 6, Eltseq(ext_rho_T1.1)), T1);
phi_2 := MapFromMatrix(Matrix(F, 6, 6, Eltseq(ext_rho_T2.1)), T2);
print "Computation 7.5(c): the extensions of rho to T_1 and to T_2 form 1-dimensional spaces, spanned by phi_1, phi_2.";
// (d) t_i in T_i and b in J_0 with (t_i^2, b) <> 0 and (t_i^2, b) / ((t_i^{phi_i})^2, b) = c_i^2, c_i rational
J0_in_U := J0@BasisMatrix(J);            // J_0 as a subspace of U
sq_pair := function(i1, i2, j)
   y1 := Ualg!T1.i1; y2 := Ualg!T2.i2; bb := Ualg!J0_in_U.j;
   return FrobeniusFormAtElements(y1*y1, bb, form_U) ne 0 and FrobeniusFormAtElements(y2*y2, bb, form_U) ne 0;
end function;
assert exists(wit){ <i1, i2, j> : i1 in [1..6], i2 in [1..6], j in [1..14] | sq_pair(i1, i2, j) };
t1 := Ualg!T1.(wit[1]);
t2 := Ualg!T2.(wit[2]);
b := Ualg!J0_in_U.(wit[3]);
t1_im := Ualg!(T1.(wit[1])@phi_1);
t2_im := Ualg!(T2.(wit[2])@phi_2);
ratio_1 := FrobeniusFormAtElements(t1*t1, b, form_U) / FrobeniusFormAtElements(t1_im*t1_im, b, form_U);
ratio_2 := FrobeniusFormAtElements(t2*t2, b, form_U) / FrobeniusFormAtElements(t2_im*t2_im, b, form_U);
is_sq1, c1 := IsSquare(ratio_1);
is_sq2, c2 := IsSquare(ratio_2);
assert is_sq1 and is_sq2;
printf "Computation 7.5(d): t_1 = T_1.%o, t_2 = T_2.%o, b = J_0.%o; (t_1^2,b) = %o, (t_2^2,b) = %o; ratios %o = (%o)^2 and %o = (%o)^2.\n",
   wit[1], wit[2], wit[3], FrobeniusFormAtElements(t1*t1, b, form_U), FrobeniusFormAtElements(t2*t2, b, form_U),
   ratio_1, c1, ratio_2, c2;
// (e) none of the four maps (rho on J, lambda_1 phi_1 on T_1, lambda_2 phi_2 on T_2), (lambda_1, lambda_2) in {+-c_1} x {+-c_2},
//     extends to an automorphism of U. Since <<T>> = U, an extension is determined by the map on T = T_1 + T_2;
//     we check that no automorphism of U at all extends the map on T.
L_in := [Ualg!T1.i : i in [1..6]] cat [Ualg!T2.i : i in [1..6]];
for signs in [<1,1>, <1,-1>, <-1,1>, <-1,-1>] do
   l1 := signs[1]*c1;
   l2 := signs[2]*c2;
   L_out := [l1*Ualg!(T1.i@phi_1) : i in [1..6]] cat [l2*Ualg!(T2.i@phi_2) : i in [1..6]];
   t0 := Begin("attempt to extend the map to an automorphism -> ext");
   bool, ext := ExtendMapToAlgebraAutomorphism(L_in, L_out);
   Timed("attempt to extend the map to an automorphism -> ext", t0);
   assert not bool;
   printf "Computation 7.5(e): (lambda_1, lambda_2) = (%o, %o): no automorphism of U extends this map.\n", l1, l2;
end for;

Section("Computation 7.7", t_start);
K := Eigenspace(ad_a, 1/32);
nK := 132;
assert Dimension(K) eq nK;
// (a) <<K>> = A
t0 := Begin("subalgebra generated by K");
assert VectorSpace(A) eq Subalgebra({@ A!K.i : i in [1..nK] @});
Timed("subalgebra generated by K", t0);
print "Computation 7.7(a): <<K>> = A.";
//
// (b) the extensions of id_U to K form a 1-dimensional space.
//
// A linear map phi of K extends id_U, i.e. (uk)^phi = u k^phi for all u in U, k in K (recall UK is contained in K
// by the fusion law), if and only if phi commutes with the restriction ad_u|_K for every u in U. Hence the space
// of extensions of id_U is the commutant in End(K) of {ad_u|_K : u in U}; it is contained in the commutant of
// ad_{u_1}|_K, ..., ad_{u_m}|_K for any choice of u_1, ..., u_m in U, and it always contains the scalar maps.
// So it suffices to exhibit elements u_j of U for which this smaller commutant is 1-dimensional.
//
// The commutant of a few 132 x 132 matrices M_1, ..., M_m is computed by the cyclic-vector method rather than by
// solving for the 132^2 entries of phi: if a vector k_0 generates K under the M_j (i.e. the vectors k_0 W, for words
// W in the M_j, span K), then a map phi commuting with all M_j is determined by x := k_0^phi, via (k_0 W)^phi = x W.
// Choose a basis k_0 W_1, ..., k_0 W_132 of K obtained by spinning k_0. For each basis vector k_0 W_i and each M_j,
// write (k_0 W_i) M_j = sum_l c_l (k_0 W_l); then phi commutes with M_j on k_0 W_i if and only if
//      x (sum_l c_l W_l - W_i M_j) = 0,
// a homogeneous linear condition on the 132 coordinates of x. Conversely, every x satisfying all these conditions
// defines (by (k_0 W_l)^phi := x W_l) a map commuting with every M_j. Thus the dimension of the commutant equals the
// dimension of the common solution space of these conditions, and x = k_0 (phi = id) is always a solution. As soon as
// the solution space has dimension 1, we are done: the commutant, and a fortiori the space of extensions of id_U,
// consists of the scalar maps.
//
// All choices are deterministic: u_m := sum_i ((m i mod 101) + 1) U.i for m = 1, 2, ..., and k_0 runs through the
// basis vectors of K until a cyclic one is found. The choices actually used are reported. If the commutant of the
// first three u_m were larger than 1-dimensional (it is not), further u_m would be added.
//
BK := BasisMatrix(K);
VK := VectorSpace(F, nK);
// coordinates w.r.t. the basis of K of the matrix of ad_u restricted to K (row convention: coordinate vector of k
// times AdOnK(u) is the coordinate vector of u*k), computed from the algebra product and scaled to an integer matrix
// (scaling by a nonzero constant does not change the commutant)
AdOnK := function(u)
   prods := Matrix([Vector(u*(A!K.i)) : i in [1..nK]]);
   bool, M := IsConsistent(BK, prods);      // M*BK = prods
   assert bool;                             // u*K is contained in K
   return LCM([Denominator(x) : x in Eltseq(M)])*M;
end function;
Ugen := func< m | &+[ (((m*i) mod 101) + 1) * (A!U.i) : i in [1..128] ] >;
// spin k_0 under mats; return whether k_0 is cyclic, the spun basis, the words W_l, and the set of tree edges
Spin := function(k0, mats)
   basis := [k0];
   words := [IdentityMatrix(F, nK)];
   tree := { car< Integers(), Integers() > | };
   Wsp := sub< VK | k0 >;
   i := 1;
   while i le #basis and Dimension(Wsp) lt nK do
      for j in [1..#mats] do
         y := basis[i]*mats[j];
         if y notin Wsp then
            Append(~basis, y);
            Append(~words, words[i]*mats[j]);
            Include(~tree, <i, j>);
            Wsp := Wsp + sub< VK | y >;
         end if;
      end for;
      i +:= 1;
   end while;
   return Dimension(Wsp) eq nK, basis, words, tree;
end function;
// the commutant of mats as the solution space for x = k_0^phi; stops as soon as the dimension is 1
Commutant := function(mats, basis, words, tree)
   Bm := Matrix(basis);
   Ker := VK;
   used := 0;
   for i in [1..nK] do
      for j in [1..#mats] do
         if <i, j> in tree then continue; end if;      // tree edges give trivial conditions
         y := basis[i]*mats[j];
         bool, c := IsConsistent(Bm, y);              // c*Bm = y
         assert bool;
         N := -words[i]*mats[j];
         for l in Support(c) do
            N +:= c[l]*words[l];
         end for;
         Ker := Ker meet sub< VK | Basis(Kernel(N)) >;   // Kernel(N) = { x : x*N = 0 }
         used +:= 1;
         if Dimension(Ker) eq 1 then
            return Ker, used;
         end if;
      end for;
   end for;
   return Ker, used;
end function;
t0 := Begin("commutant of ad_{u_j}|_K by the cyclic-vector method -> Ker");
done := false;
mats := [];
for m in [1..8] do
   Append(~mats, AdOnK(Ugen(m)));
   if m lt 3 then continue; end if;
   assert exists(i0){ i : i in [1..nK] | Spin(VK.i, mats) };
   cyc, basis, words, tree := Spin(VK.i0, mats);
   assert cyc;
   Ker, used := Commutant(mats, basis, words, tree);
   assert VK.i0 in Ker;                                 // x = k_0, i.e. phi = id, is always a solution
   printf "Computation 7.7(b): u_1, ..., u_%o as in the comments; k_0 = K.%o is cyclic; after %o conditions the commutant of the ad_{u_j}|_K has dimension %o.\n",
      m, i0, used, Dimension(Ker);
   if Dimension(Ker) eq 1 then
      done := true;
      break;
   end if;
end for;
Timed("commutant of ad_{u_j}|_K by the cyclic-vector method -> Ker", t0);
assert done;
print "Computation 7.7(b): the extensions of id_U to K form a 1-dimensional space, consisting of the scalar maps.";
// (c) (k^2, u_0) <> 0 for some k in K, u_0 in U (deterministic search over basis vectors)
assert exists(witK){ <i, j> : i in [1..nK], j in [1..128] | FrobeniusFormAtElements((A!K.i)*(A!K.i), A!U.j, form) ne 0 };
printf "Computation 7.7(c): (k^2, u_0) <> 0 for k = basis vector %o of K and u_0 = basis vector %o of U.\n", witK[1], witK[2];

Section("Remark on exactness (after Proposition 7.8)", t_start);
// P acts trivially on J; the elements of S \ P induce rho on J
Jmaps_P := {RestrictMapToSubspace(Matrix(x), Jb) : x in [z, z1, z2, z3, z4]};
assert Jmaps_P eq {IdentityMatrix(F, 26)};
S_minus_P := [x : x in S | x notin P];
assert #S_minus_P eq 8;
Jmaps_SP := {RestrictMapToSubspace(Matrix(x), Jb) : x in S_minus_P};
assert #Jmaps_SP eq 1;
// compare with rho, both expressed in the basis of J: RestrictMapToSubspace returns the matrix w.r.t. the basis of Jb
assert Jmaps_SP eq {rho};
print "Remark: P acts trivially on J and every element of S \\ P induces rho on J.";
// tau_v = z_3|_U = z_4|_U and tau_w = z_1|_U = z_2|_U
tau_v := TauMapMonster(v_s : values := <3/10, 1/20>);
tau_w := TauMapMonster(w_s : values := <3/10, 1/20>);
zU := [RestrictMapToSubspace(Matrix(x), U) : x in [z1, z2, z3, z4]];
assert zU[3] eq zU[4] and zU[1] eq zU[2];
assert tau_v eq zU[3] and tau_w eq zU[1];
print "Remark: tau_v = z_3|_U = z_4|_U and tau_w = z_1|_U = z_2|_U.";

Section("Done (Computation 7.11 is in Lemma_6_27.m / IsSixTranspositionClass.m)", t_start);
printf "Total CPU time: %o s\n", Cputime(t_start);
UnsetLogFile();
