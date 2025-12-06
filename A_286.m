
// load "~/Automorphisms/M11_6A4B5A.txt"; // perhaps change when a reecord is produced?
 Attach("Automorphisms.m");
 SetVerbose("Automorphisms", 1);
 SetVerbose("Fusion_check",1); 
 F := Rationals();
 //A := Algebra<F, 286 | structs>;
 //form := Matrix(form);
 A := eval Read("A_286");
 form := eval Read("form_286");
 axes := [A.i : i in [1..286] | IsIdempotent(A.i) ];
 time assert HasMonsterFusionLaw(axes[1]);
 assert #axes eq 165;
 // Computation 6.1 
 a := axes[1];
 ad_a := AdMat(a);
 assert Eigenvalues(ad_a) eq {<1, 1>, <0, 128>, <1/4, 25>, <1/32, 132> };
 
 // Computation 6.2
 
 // (a)
 time G_p, G, isom, gpname := MiyamotoGroup(axes);
 time jordans := JordanAxes(A, [Matrix(g) : g in Generators(G)]: form := form);
 assert IsEmpty(jordans);
 
 // (b)
 time twins := FindTwins(a: form := form);
 assert IsEmpty(twins);
 
 // Set up 6.3 and beyond
 S := SylowSubgroup(G_p, 2)@isom;
 invs_S := [ x : x in ConjugacyClasses(S) | x[1] eq 2];
 assert #invs_S eq 2;
 assert exists(cent_class){ x : x in invs_S | x[2] eq 1};
 z := cent_class[3];
 assert exists(other){ x : x in invs_S | x[2] ne 1};
 C := Class(S, other[3]);
 P := sub<S | C join {z}>;
 assert Order(P) eq 8;
 invs_P := [ x : x in ConjugacyClasses(P) |x[1] eq 2];
 assert #invs_P eq 3;
 twos := [x : x in invs_P | x[2] ne 1];
 assert #twos eq 2;
 assert &join[x[3]^P :x in twos ] eq C;
 // the route I wanted to take and abandoned was to use the permutation form of P to define an action on C and show that it has two orbits
 assert P eq sub<P | [x[3] : x in twos ]>;
 //time bool, ax_z := IsInducedFromAxis(A, Matrix(z):form := form, automorphism_check := false);
// this is a bit slow, taking : Time: 333.890
// assert bool;
// assert #ax_z eq 1;
// a := ax_z[1];
 time taus := [TauMapMonster(axes[i]) : i in [1..165]]; // takes under a minute
 a :=axes[Index(taus, Matrix(z))];
 assert TauMapMonster(a) eq Matrix(z);

 assert exists(z1){ t : t in taus | t eq Matrix(twos[1][3]) };
 // way faster way than using IsInducedFromAxis
 
 a1 :=axes[Index(taus, z1)];
 assert TauMapMonster(a1) eq z1;
 assert exists(g){ g : g in P | (twos[1][3])^g ne twos[1][3]}; 
 z2 := Matrix((P!z1)^g);
 a2 :=axes[Index(taus, z2)];
 assert TauMapMonster(a2) eq z2;
 assert exists(z3){ t : t in taus | t eq Matrix(twos[2][3]) };
 a3 :=axes[Index(taus, z3)];
 assert TauMapMonster(a3) eq z3;
 assert exists(g){ g : g in P | (twos[2][3])^g ne twos[2][3]}; 
 z4 := Matrix((P!z3)^g);
 a4 :=axes[Index(taus, z4)];
 assert TauMapMonster(a4) eq z4;
 ad_a := AdMat(a);
 U := Eigenspace(ad_a, 0);
 time Ualg := Algebra<F, 128 | AllStructureConstants(FindStructureConstantsSubalgebra(A, U))>;
 e := 4/5*(&+[ a1, a2,a3, a4])+3/5*a;
 assert IsIdempotent(e);
 assert forall{x : x in [a, a1, a2, a3, a4] | x*e eq x};
 // Thus e acts as identity on the set {a}\cup _i{a_i} and hence the subalgebra it generates
 u := e-a;
 assert u in U;
 u_s := Ualg!(u@@BasisMatrix(U));
 assert IsIdempotent(u_s);
 
// time bool, form_U := HasFrobeniusForm(Ualg);
 form_U := RestrictedForm(form, U);
 // Computation 6.3
 // Part (a)
 ad_e := AdMat(e);
 ad_eU := RestrictMapToSubspace(ad_e, U);
 ad_uU := AdMat(u_s);
 assert ad_eU eq ad_uU;
 assert Eigenvalues(ad_uU) eq {< 1, 2>, <0, 26>, <3/10, 14>, <7/20, 12>, <1/20, 50>, <1/10, 24>};

 // Part (b)
 U1_e := Eigenspace(ad_uU, 1);
 U0_e := Eigenspace(ad_uU, 0);
 assert IsSubalgebra(Ualg, U1_e);
 assert IsSubalgebra(Ualg, U0_e);
 
 // Recall that we have V := <a, a_1, a_2> and V:= <a, a_3, a_4> both 2A subalgebra of E\cong 4B spanned by {a, a_1, a_2, a_3, a_a}
 one_V := 4/5*(&+[ a, a1, a2]);
 assert forall{ x : x in [a, a1, a2] |x*one_V eq x};
 one_W := 4/5*(&+[ a, a3, a4]);
 assert forall{ x : x in [a, a3, a4] |x*one_W eq x};
 v := e-one_V;
 w := e-one_W;

 v_s := Ualg!(v@@BasisMatrix(U));
 w_s := Ualg!(w@@BasisMatrix(U));
 assert v_s in U1_e;
 assert w_s in U1_e;
 assert LengthOfElement(v_s, form_U) eq 7/5;

 assert LengthOfElement(w_s, form_U) eq 7/5;
 assert LengthOfElement(u_s, form_U) eq 14/5;
 assert v*w eq 0;
 assert Dimension(Subalgebra({@a1, a3@})) eq 5; 
 assert Dimension(Subalgebra({@a1, a4@})) eq 5; 
 assert a1*a3 eq 1/64*(a1 +a3-a2-a4+a);
 ad_vU :=AdMat(v_s); 
 ad_wU :=AdMat(w_s); 
 // Cmputation 6.4 assert Eigenvalues 
 
 // Part (a)
 assert Eigenvalues(ad_vU) eq {<1,1>, <0, 59>, <3/10, 13>, <1/20,55>};
 assert Eigenvalues(ad_wU) eq {<1,1>, <0, 59>, <3/10, 13>, <1/20,55>};

 // Part (b)
 assert HasAlmostMonsterFusionLaw(w_s:arbitrary_parameters :=<3/10, 1/20>); 

 // Part (c)
 tau_v := TauMapMonster(v_s:values := <3/10, 1/20>);
 z1_U := RestrictMapToSubspace(z1, U);
 z2_U := RestrictMapToSubspace(z2, U);
 z3_U := RestrictMapToSubspace(z3, U);
 z4_U := RestrictMapToSubspace(z4, U);
 assert z3_U eq z4_U;
 tau_w := TauMapMonster(w_s:values := <3/10, 1/20>);
 assert tau_v eq z3_U;
 assert tau_w eq z1_U;
 
 J := U0_e;
 assert Dimension(J) eq 26;
 
 // Computation 6.5 (a)
 time P_restrictedToJ := {RestrictMapToSubspace(x, J@BasisMatrix(U)) : x in [Matrix(z), z1, z2, z3, z4]}; 
 assert #P_restrictedToJ eq 1;

 assert forall{x : x in P_restrictedToJ | IsIdentity(x)}; 
 // hence P is identity on J
 S_P := {x : x in S | x notin P};
 #S_P;

 S_minusP_restrictedToJ := { RestrictMapToSubspace(Matrix(x), J@BasisMatrix(U)) : x in S_P};
 assert #S_minusP_restrictedToJ eq 1;

 assert forall{x : x in S_minusP_restrictedToJ | not IsIdentity(x)};
 assert Order(MatrixGroup<26, F| S_minusP_restrictedToJ>) eq 2;
 Jalg := Algebra<F, 26 | AllStructureConstants(FindStructureConstantsSubalgebra(Ualg, J))>;
 J0 := FindFixedSubalgebra(Jalg, SetToSequence(S_minusP_restrictedToJ));
 assert Dimension(J0) eq 14;
 
 // Computation 6.6 (a)

 A0_u := Eigenspace(AdMat(u), 0);
 assert Dimension(A0_u) eq 30;
 K := FindPerpWithRespectToForm(A, A0_u, J@BasisMatrix(U): form := form );
 assert Dimension(K) eq 4;
 assert forall{i : i in [1..4] | forall{j : j in [1..26] | FrobeniusFormAtElements(A!(J@BasisMatrix(U)).j, A!K.i, form) eq 0}};
 squares_K := [ x*x where x:= A!K.i : i in [1..4]]; 
 J0b := (J0@BasisMatrix(J))@BasisMatrix(U);
 Degree(J0b);
 Jb := J@BasisMatrix(U);
 ProjJb := ProjectionToSubspace(A, Jb, form);
 squares_Kprojs := {x*ProjJb : x in squares_K};
 assert forall{x : x in squares_Kprojs | x in Jb};
 assert Subalgebra(IndexedSet(squares_Kprojs)) eq J0b;
 // Remark: We may perform the above by forming the algebra version of $A_0(u)$ and
 // then working in this smaller algebra, however, we already had the things
 // for A in place and so it was more convenient, albeit a bit slow 

 rest := MapFromMatrix(IndexedSet(S_minusP_restrictedToJ)[1], Jb);
 assert forall{i : i in [1..14] | J0b.i@rest eq J0b.i};
 
 // Remarks after Computation 6. 6
 K0 := FindPerpWithRespectToForm(A, K, sub<K| Vector(a)> :form := form);
 assert Dimension(K0) eq 3;
 assert forall{i : i in [1..3] |FrobeniusFormAtElements(A!K0.1, a, form) eq 0 };
 assert a in K;
 assert K0 subset Eigenspace(ad_a, 1/4);
 [K0.i*(IndexedSet(S_P)[1]) eq K0.i : i in [1..3]];
 [K0.i*(IndexedSet(S_P)[3]) eq K0.i : i in [1..3]];
 [K0.i*(IndexedSet(S_P)[4]) eq K0.i : i in [1..3]];
 [K0.i*(IndexedSet(S_P)[5]) eq -K0.i : i in [1..3]];
 [K0.i*(IndexedSet(S_P)[6]) eq -K0.i : i in [1..3]];
 [K0.i*(IndexedSet(S_P)[7]) eq K0.i : i in [1..3]];
 [K0.i*(IndexedSet(S_P)[8]) eq -K0.i : i in [1..3]];
 // so some elements from S\P negate K0, while the others fix K0. Depending on the run, 
 // rhe signs may change. The key thing is that an automorphism either fixes or negates all $K_0$
 
 // Computation 6.8 (a)
 J0alg := Algebra<F, 14 | AllStructureConstants(FindStructureConstantsSubalgebra(Jalg, J0))>;
 form_J0 := RestrictedForm(form, J0b);
 form_J := RestrictedForm(form, Jb);

 time twenty_six_fifths := FindAllIdempotents(J0alg, VectorSpace(J0alg): length := 26/5, form := form_J0);
 assert #twenty_six_fifths eq 1;
 time thirty_six_fifths := FindAllIdempotents(J0alg, VectorSpace(J0alg): length := 36/5, form := form_J0);
 assert #thirty_six_fifths eq 1;
 assert Subalgebra(thirty_six_fifths join twenty_six_fifths) eq VectorSpace(J0alg);
 B := FindPerpWithRespectToForm(Jalg, VectorSpace(Jalg), J0: form := form_J);
 assert Dimension(B) eq 12;
 assert forall{i : i in [1..14] | forall{ j : j in [1..12] | FrobeniusFormAtElements(Jalg!J0.i, Jalg!B.j, form_J) eq 0}};
 
 // Computation 6.10 (a)
 time bool, ext_J0_B := ExtendAutToMod(Jalg, J0, B, IdentityMatrix(F, 14));
 assert bool;
 assert Dimension(ext_J0_B) eq 1;

 // 6.10 (b)
 ProjJ0 := ProjectionToSubspace(Jalg, J0, form_J);
 assert exists(b){ b : b in Basis(B) | (b*b)*ProjJ0 ne 0};
 
 T := Eigenspace(ad_eU, 7/20);
 assert Dimension(T) eq 12;
 
 // Computation 6.12
 time assert Dimension(Subalgebra({@Ualg!T.i : i in [1..12] @})) eq 128;

 T1 := Eigenspace(ad_vU, 3/10) meet Eigenspace(ad_wU, 1/20); 
 assert Dimension(T1) eq 6;
 T2 := Eigenspace(ad_vU, 1/20) meet Eigenspace(ad_wU, 3/10); 
 assert T1 +T2 eq T;
 S_restU := {@ RestrictMapToSubspace(Matrix(x), U) : x in S_P @};
 assert forall{x : x in S_restU | v_s*x eq w_s and w_s*x eq v_s};
 assert forall{x : x in S_restU | T1*x eq T2 and T2*x eq T1};
 assert #S_minusP_restrictedToJ eq 1;
 rho := IndexedSet(S_minusP_restrictedToJ)[1];
 assert forall{i : i in [1..12] | B.i*rho eq -B.i};
 // Computation 6.13 (a)
 bool, ext_rho_T1 := ExtendAutToMod(Ualg, J, T1, rho); 
 assert bool;
 assert Dimension(ext_rho_T1) eq 1;
 time bool, ext_rho_T2 := ExtendAutToMod(Ualg, J, T2, rho); 
 assert bool;
 assert Dimension(ext_rho_T2) eq 1;
 
 // 6.13 (b)
 t1 := Ualg!T1.1;
 t2 := Ualg!T2.1;
 b := Ualg!(J0@BasisMatrix(J)).1;
 assert FrobeniusFormAtElements(t1*t1, b, form_U) ne 0;
 assert FrobeniusFormAtElements(t2*t2, b, form_U) ne 0;

 rho_map := MapFromMatrix(rho, J);
 phi_1 := MapFromMatrix(Matrix(F, 6, 6, Eltseq(ext_rho_T1.1)), T1);
 phi_2 := MapFromMatrix(Matrix(F, 6, 6, Eltseq(ext_rho_T2.1)), T2);
 lambda_1_sq := ((FrobeniusFormAtElements(t1*t1, b, form_U)/FrobeniusFormAtElements(t1_im*t1_im, b, form_U))) where t1_im := Ualg!(t1@phi_1);
 bool, c1 := IsSquare(lambda_1_sq);
 assert bool;
 c1;
 lambda_2_sq := ((FrobeniusFormAtElements(t2*t2, b, form_U)/FrobeniusFormAtElements(t2_im*t2_im, b, form_U))) where t2_im := Ualg!(t2@phi_2);
 assert bool;
 bool, c2 := IsSquare(lambda_2_sq);
 assert bool;
 c2;
 // We were basically implementing Equation (1) of Lemma 6.14 
 assert c1^2 eq lambda_1_sq;
 assert c2^2 eq lambda_2_sq;
 
 // Computation 6.15 
 // we start with $(\lamba_1, \lambda_2) = (c_1, c_2)$.
 L_inT1 := [ Ualg!T1.i : i in [1..6]];
 L_ouT1a := [ c1*Ualg!T1.i : i in [1..6]];
 L_inT2 := [ Ualg!T2.i : i in [1..6]];
 L_ouT2a := [ c1*Ualg!T2.i : i in [1..6]];
 L_ouT1a := [ c1*Ualg!(T1.i@phi_1) : i in [1..6]];
 L_ouT2a := [ c2*Ualg!(T2.i@phi_2) : i in [1..6]];
 assert forall{i : i in [1..6] | LengthOfElement(L_inT1[i], form_U) eq LengthOfElement(L_ouT1a[i], form_U)};
 assert forall{i : i in [1..6] | LengthOfElement(L_inT2[i], form_U) eq LengthOfElement(L_ouT2a[i], form_U)};
 time bool, ext_rhos := ExtendMapToAlgebraAutomorphism(L_inT1 cat L_inT2, L_ouT1a cat L_ouT2a);
 assert not bool;
 // thus doesn't give rise to an automorphism of U
 
 // we now consider the case $(\lambda_1, \lambda_2)=(c_1, -c_2)$.
 L_ouT2b := [ -c2*Ualg!(T2.i@phi_2) : i in [1..6]];
 time bool, ext_rhos := ExtendMapToAlgebraAutomorphism(L_inT1 cat L_inT2, L_ouT1a cat L_ouT2b);
 assert not bool;
 // again we get no automorphism of U
 
 // the case $(\lambda_1, \lambda_2)=(-c1, c2);
 L_ouT1b := [ -c1*Ualg!(T1.i@phi_1) : i in [1..6]];
 time bool, ext_rhos := ExtendMapToAlgebraAutomorphism(L_inT1 cat L_inT2, L_ouT1b cat L_ouT2a);
 assert not bool;
 // again this results in no automorphism of U
 
 // finally we consider the case $(\lambda_1, \lambda_2)=(-c1, -c2)$
 time bool, ext_rhos := ExtendMapToAlgebraAutomorphism(L_inT1 cat L_inT2, L_ouT1b cat L_ouT2b);
 assert not bool;
 //so it doesn't give rise to an automorphism 
 
 // Computation 6.17
 time bool, ext_id_T1 := ExtendAutToMod(Ualg, J, T1, IdentityMatrix(F, Dimension(J))); 
 assert bool;
 assert Dimension(ext_id_T1) eq 1;
 time bool, ext_id_T2 := ExtendAutToMod(Ualg, J, T2, IdentityMatrix(F, Dimension(J))); 
 assert bool;
 assert Dimension(ext_id_T2) eq 1;
 assert IsIdentity(Matrix(F, 6, 6, Eltseq(ext_id_T1.1)));
 assert IsIdentity(Matrix(F, 6, 6, Eltseq(ext_id_T2.1)));
 
 // We now recycle the use of K
 K := Eigenspace(ad_a, 1/32); 
 // Computation 6.19 (a)
 assert VectorSpace(A) eq Subalgebra({@A!K.i : i in [1..132] @});
 
 // Computation 6.19 (b)
 time bool, ext_id_K := ExtendAutToMod(A, U, K, IdentityMatrix(F, Dimension(U))); 
 assert bool;
 assert Dimension(ext_id_K) eq 1;
 
 // Computation 6.19 (c)

 k := A!(K.Random({1..132}));
 u_0 := A!(Random({1..128}));
 assert FrobeniusFormAtElements(k*k, u, form) ne 0;
 
 // the algebra parts of the computation are done!
