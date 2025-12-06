
 Attach("Automorphisms.m");
 SetVerbose("Automorphisms",1);
 A := eval Read("A_76");
 A;
 axes := [A.i :i in [1..76] | IsIdempotent(A.i) ];
 assert HasMonsterFusionLaw(axes[1]);
 time Miy_p, Miy, isom, gpname := MiyamotoGroup(axes);
 gpname;
 time bool, form := HasFrobeniusForm(A);
 assert bool;
 assert Dimension(form) eq 1;
 F := BaseField(A);
 form := Matrix(F, 76, 76, Eltseq(form.1));
 lm := LengthOfElement(axes[1], form);
 form := 1/lm*form;
 assert LengthOfElement(axes[1], form) eq 1;
 S := SylowSubgroup(Miy, 2);
 GroupName(S);
 subs4 := Subgroups(S:OrderEqual:=4);
 #subs4;
 [GroupName(x`subgroup) : x in subs4]; 
 Y := {@y : y in axes| TauMapMonster(y) in subs4[2]`subgroup @};
 #Y;
 V := Subalgebra(Y);
 assert Order(&*[TauMapMonster(x) : x in Y[[1,2]]]) eq 2;
 assert Y[1]*Y[2] eq 1/8*(Y[1]+Y[2]-Y[3]);
 assert Y[1]*Y[3] eq 1/8*(Y[1]-Y[2]+Y[3]);
 assert Y[2]*Y[3] eq 1/8*(-Y[1]+Y[2]+Y[3]);
 // Thus Y generates 2A
 E := sub<G | [TauMapMonster(x) : x in Y]>;
 GroupName(E);
// Computation 4.1 (a) 
 time jordans := JordanAxes(A, [Matrix(x):x in Generators(Miy)]: form :=form);
 assert #jordans eq 0;
 // Part (b)
 time twins := FindTwins(axes[1]:form := form);
 assert #twins eq 0;
 // Part (c) We could use GroupFromAxes here to get that the group is $A_6{.}2^2$
 aut := AutomorphismGroup(Miy_p);
 Order(aut);
 out := [x : x in Generators(aut) | not IsInnerAutomorphism(x)];
 #out;

 //There is a one-to-one corresopndence between tau involutions and axes.
 invs_perms := [TauMapMonster(axes[i])@@isom : i in [1..#axes]];
 x1 := [Position(invs_perms, invs_perms[i]@out[1]) : i in [1..45]];
 assert not IsCoercible(Miy_p, x1);
 x2 := [Position(invs_perms, invs_perms[i]@out[2]) : i in [1..45]];
 assert not IsCoercible(Miy_p, x2);
 out1 := Sym(#axes)!x1;
 out2 := Sym(#axes)!x2;
 Order(out1);
 Order(out2);
 bool, ext1 := ExtendMapToAlgebraAutomorphism(axes, [axes[i^out1] : i in [1..45]]); 
 assert bool;
 Order(ext1);

 time bool, ext2 := ExtendMapToAlgebraAutomorphism(axes, [axes[i^out2] : i in [1..45]]); 
 assert bool;
 Order(ext2);
 G := MatrixGroup< 76, F|Miy, ext1, ext2>;
 Order(G);
 assert GroupName(G) in {"A6.C2^2", "S6.C2"}; 
 invsG := [x : x in ConjugacyClasses(G) | x[1] eq 2];
 #invsG;
 assert {x[2]: x in invsG} eq {45,30,36};
 i_30 := [i : i in [1..3] | invsG[i][2] eq 30][1];
 i_36 := [i : i in [1..3] | invsG[i][2] eq 36][1];

 // This is computation 4.2 

 time IsInducedFromAxis(A, Matrix(invsG[i_30][3]): form := form, automorphism_check := false);
 time IsInducedFromAxis(A, Matrix(invsG[i_36][3]): form := form, automorphism_check := false);

 // Computation 4.3 now
 decomps := JointEigenspaceDecomposition(Y);
 assert Keys(decomps) eq {[0,0,0],[1/4, 1/32, 1/32], [1/32, 1/4, 1/32], [1/32, 1/32, 1/4], [0, 1/32, 1/32], [1/32, 0, 1/32], [1/32, 1/32,0]};
 // Part (a)
 assert Dimension(decomps[[0,0,0]]) eq 15; 

 // Part (b) 
 // (i)
 assert forall{x : x in {[1/4, 1/32, 1/32], [1/32, 1/4, 1/32], [1/32, 1/32, 1 /4]} | Dimension(decomps[x]) eq  5};
 // (ii)
 assert forall{x : x in {[0, 1/32, 1/32], [1/32, 0, 1/32], [1/32, 1/32, 0]} | Dimension(decomps[x]) eq  11};

 // The assertion that the sum of the parts is not A is obvious from the dimensions

 assert &+[decomps[x] : x in Keys(decomps)] ne VectorSpace(A);
 // The computation of Aut(U) requires the form to be unique.
 U := decomps[[0,0,0]];
 form_Urest := RestrictedForm( form, U);
 time Ualg := Algebra<F, 15|AllStructureConstants(FindStructureConstantsSubalgebra(A, U))>;
 N := Normaliser(G, E);
 gensN := SetToSequence(Generators(N));
 gensN_s := [RestrictMapToSubspace(Matrix(x), U): x in gensN];
 gensN_s := [Matrix(x) : x in gensN_s| not IsIdentity(x)];
 U_N := FindFixedSubalgebra(Ualg, gensN_s);
 assert Dimension(U_N) eq 5;
 twos_in_N := FindAllIdempotents(Ualg, U_N: length := 2, form := form_Urest); 
 assert #twos_in_N eq 1;
 d := twos_in_N[1];
 // Computation 4.4 (a)
 time bool, form_U := HasFrobeniusForm(Ualg);
 assert bool;
 assert Dimension(form_U) eq 1;
 assert IsAssociatingForm(Ualg, form_Urest);

 // Computation 4.4 (b)
 time twos_in_U := FindAllIdempotents(Ualg, VectorSpace(Ualg): length := 2, form := form_Urest);
 assert #twos_in_U eq 1;
 d in twos_in_U;
 // Computation 4.4 (c)
 ad_d := AdMat(d);
 assert Eigenvalues(ad_d) eq {<1,1>, <0,7>, <1/2, 3>, <1/8,4>};
 d_big := A!(d@BasisMatrix(U));
 assert IsIdempotent(d_big);

 ad_dbig := AdMat(d_big);
 assert Eigenvalues(ad_dbig) eq {<1,1>, <0,34>, <1/2, 9>, <1/8,32>};

 // Computation 4.4 (d)
 SetVerbose("Fusion_check",1);
 assert HasAlmostMonsterFusionLaw(d: arbitrary_parameters := <1/2, 1/8>);
 assert HasAlmostMonsterFusionLaw(d_big: arbitrary_parameters := <1/2, 1/8>);

 // Remark 4.5
 z := TauMap(d_big, <[1,0,1/2], [1/8]>);
 assert z in G;
 assert not z in Miy;
 d_ims := Vector(d_big)^G;
 #d_ims;
 assert Dimension(Subalgebra({@A!x :x in d_ims @})) eq 76;
 // For the purposes of this computation we will denote by UU the subalgebra $U_0(d)$.
 UU := Eigenspace(ad_d, 0);
 UU_alg := Algebra<F, 7|AllStructureConstants(FindStructureConstantsSubalgebra(Ualg, UU))>;
 // This is computation 4.6 (a)
 time bool, form_UUv := HasFrobeniusForm(UU_alg);
 assert bool;
 assert Dimension(form_UUv) eq 1;
 form_UU := RestrictedForm(form_Urest, UU);

 // Computation 4.6 (b)
 time seventeen_fifths := FindAllIdempotents(UU_alg, VectorSpace(UU_alg): length := 17/5, form := form_UU);
 assert #seventeen_fifths eq 3;

 // Computation 4.6 (c)
 assert Subalgebra(seventeen_fifths) eq VectorSpace(UU_alg);

 // This is Computation 4.6 (d)
 assert forall{v : v in seventeen_fifths | Eigenvalues(AdMat(v)) eq {<1,1>, <0,2>, <1/10, 1>, <13/30, 1>, <1/20, 1>, <7/20, 1>}};

 // Computation 4.6 (e) 
 taus_vs := [TauMap(seventeen_fifths[i], <[1, 0, 1/10, 13/30],[1/20, 7/20]>): i in [1..3]];
 assert forall{t : t in taus_vs| Order(t) eq 2 and IsAutomorphism(UU_alg, t)};

 // Computation 4.8
 W := Eigenspace(ad_d, 1/8);

 // part (a)
 assert Subalgebra({@ Ualg!W.i : i in [1.. Dimension(W)] @}) eq VectorSpace(Ualg);
 Dimension(UU);

 // Computation 4.8 (b)
 time bool, ext_W := ExtendAutToMod(Ualg, UU, W, IdentityMatrix(F,7)); 
 assert bool;
 assert Dimension(ext_W) eq 1;
 ext_W := Matrix(F, k, k, Eltseq(ext_W.1)) where k:= Dimension(W);
 ext_W;

 // Computation 4.8 (c)
 assert FrobeniusFormAtElements(Ualg!UU.1, x*x, form_Urest) ne 0 where x := Ualg!W.1;

 // Computation 4.10 (a)
 time seven_fifths := FindAllIdempotents(Ualg, VectorSpace(Ualg): length := 7/5, form := form_Urest); 
 assert #seven_fifths eq 3;

 // Computation 4.10 (b)
 assert forall{v : v in seven_fifths | Eigenvalues(AdMat(v)) eq {<1,1>, <0,6>, <3/10, 3>,  <1/20, 5> }};

 // Computation 4.10 (c)
 assert forall{u : u in seven_fifths | HasAlmostMonsterFusionLaw(u: arbitrary_parameters := <3/10, 1/20>)};

 // Computation 4.10 (d)
 time taus_us := [TauMap(seven_fifths[i], <[1, 0, 3/10],[1/20]>): i in [1..3]];
 assert GroupName(MatrixGroup<15, F|taus_us>) eq "S3";

 // Computation 4.13
 W1 := decomps[[0, 1/32, 1/32]];
 W2 := decomps[[ 1/32,0, 1/32]];
 W3 := decomps[[ 1/32, 1/32, 0]];
 // Computation 4.13 (a)
 Ws := [W1, W2, W3];
 for W in Ws do
    time bool, ext_W := ExtendAutToMod(A, U, W, IdentityMatrix(F, 15));
    assert bool;
    assert Dimension(ext_W) eq 1;
 end for;
 Dimension(Ws[1]);

// Computation 4.13 (b)
 assert Dimension(Subalgebra({@A!W1.i : i in [1..11]@} join {@W2.i : i in [1..11]@} )) eq 76;
 assert Dimension(Subalgebra({@A!W1.i : i in [1..11]@} join {@W3.i : i in [1..11]@} )) eq 76;
 assert Dimension(Subalgebra({@A!W2.i : i in [1..11]@} join {@W3.i : i in [1..11]@} )) eq 76;

 w1 := A!W1.1;
 w2 := A!W2.1;
 w3 := A!W3.1;
 u := A!U.1;
 // Computation 4.13 (c)
 // (c) (i)
 assert FrobeniusFormAtElements(w1*w1, u, form) ne 0;
 assert FrobeniusFormAtElements(w2*w2, u, form) ne 0;
 assert FrobeniusFormAtElements(w3*w3, u, form) ne 0;
 // (c) (ii)assert FrobeniusFormAtElements(w3*w3, u, form) ne 0;
 assert FrobeniusFormAtElements(w1*w2, w3, form) ne 0;
