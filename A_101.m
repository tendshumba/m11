 SetSeed(1);
 Attach("Automorphisms.m");
 SetVerbose("Automorphisms", 1); 
 F := Rationals();
 time A_101 := eval Read("A_101");
  time bool, form_101v := HasFrobeniusForm(A_101);
 assert bool;
 assert Dimension(form_101v) eq 1; 
 form_101 := eval Read("form_101");
 axes_101 := [A_101.i : i in [1..101] | IsIdempotent(A_101.i)];
 time Miy101_p, Miy101, isom101, gpname101 := MiyamotoGroup(axes_101);
 time G_perm, G, iso_G, gpname_G, _ := GroupFromAxes(axes_101);
 GroupName(G);
 S := SylowSubgroup(G, 2);
 invs_S := [x : x in ConjugacyClasses(S) | x[1] eq 2];
 assert #invs_S eq 3;
 exists(cent){ x : x in invs_S | x[2] eq 1};
 tau_1 := cent[3];
 
 time IsInducedFromAxis(A_101, Matrix(tau_1):automorphism_check := false, form:= form_101);
 // Better to use the following
 _, a1 :=$1;

 a1 := a1[1];
 others := [x : x in invs_S | x ne cent ];
 for x in others do
    t := x[3];
    bool, X := IsInducedFromAxis(A_101, Matrix(t) : automorphism_check := false, form := form_101);
    if bool then tau_2  := t;
       assert #X eq 1;
       a_2 := X[1];
       Y := Vector(a_2)^S;
       exists(a_3){ a : a in Y | a ne a_2};
       a_3 := A_101!a_3;
       else
       print "The class is not induced by axes";
       end if;
    end for;
 Y := {@a1, a_2, a_3 @};
 assert exists(tau_3){x : x in Class(S, tau_2) | x ne tau_2};
 E := MatrixGroup<101, F | tau_1, tau_2, tau_3>;
 assert GroupName(E) eq "C2^2";

 // Computation 5.1 (a)
 time jordans := JordanAxes(A_101, [Matrix(x) : x in Generators(Miy101)]: form := form_101);

 assert IsEmpty(jordans);
 invs_G := [x : x in ConjugacyClasses(G) | x[1] eq 2];
 assert #invs_G eq 2;
 // Computation 5.1 (b)
 G0 := Miy101;
 exists(c_2A){x : x in invs_G | x[3] in G0};
 assert c_2A[2] eq 55;
 time twins := FindTwins(axes_101[1]: form := form_101);
 assert IsEmpty(twins);
 // Computation 5.1 (c)
 assert exists(c_2B){x : x in invs_G | not x[3] in G0};
 bool,_ := IsInducedFromAxis(A_101, Matrix(c_2B[3]): form := form_101, automorphism_check := false);
 assert not bool;
 // Setup for 5.2 onwards
 N := Normaliser(G0, E);
 assert GroupName(N) eq "A4";
 subs_60 := Subgroups(G0: OrderEqual := 60);
 #subs_60;
 assert forall{x : x in subs_60 | GroupName(x`subgroup) eq "A5"};
 H1 := subs_60[1]`subgroup;
 H2 := subs_60[2]`subgroup;
 W1 := SubalgebraCorrespondingToSubgroup(A_101, H1: axes := axes_101, Miyamoto_group := G0);
 assert Dimension(W1) eq 26;
 W2 := SubalgebraCorrespondingToSubgroup(A_101, H2: axes := axes_101, Miyamoto_group := G0);
 assert Dimension(W2) eq 26;

 // Computation 5.2
 decomps := JointEigenspaceDecomposition(Y);
 assert Keys(decomps) eq {[0,0,0], [1/4, 1/32, 1/32], [1/32, 1/4, 1/32], [1/32, 1/32, 1/4], [0, 1/32, 1/32], [1/32, 0, 1/32], [1/32, 1/32, 0]};
 
 // 5.2 (a)
 U := decomps[[0,0,0]];
 assert Dimension(U) eq 18; 

 // This is 5.2 (b)
 assert forall{x : x in [ [1/4, 1/32, 1/32], [1/32, 1/4, 1/32], [1/32, 1/32, 1/4]]| Dimension(decomps[x]) eq 5};

 //  5.2 (c)
 assert forall{x : x in [ [0, 1/32, 1/32], [1/32, 0, 1/32], [1/32, 1/32, 0]] | Dimension(decomps[x]) eq 17};

 // Setup for Computation 5.3 onward
 V := Subalgebra(Y);
 assert Dimension(V) eq 3;
 V_alg := Algebra<F, 3| AllStructureConstants(FindStructureConstantsSubalgebra(A_101, V))>;
 W1_alg := Algebra<F, 26| AllStructureConstants(FindStructureConstantsSubalgebra(A_101, W1))>;
 W2_alg := Algebra<F, 26| AllStructureConstants(FindStructureConstantsSubalgebra(A_101, W2))>;
 _,one_V := HasOne(V_alg); 
 _,one_W1 := HasOne(W1_alg); 
 _,one_W2 := HasOne(W2_alg); 
 one_Vb := A_101!(one_V@BasisMatrix(V));
 assert forall{y: y in Y |one_Vb*y eq y};
 one_W1b := A_101!(one_W1@BasisMatrix(W1));
 assert forall{i : i in [1..26] |one_W1b*(A_101!W1.i) eq W1.i};
 one_W2b := A_101!(one_W2@BasisMatrix(W2));
 assert forall{i : i in [1..26] |one_W2b*(A_101!W2.i) eq W2.i};
 x1 := one_W1b-one_Vb;
 x2 := one_W2b-one_Vb;
 x1 in U;
 assert exists(g1){g : g in G0| N subset H1^g };
 assert exists(g2){g : g in G0| N subset H2^g };
 H1 := H1^g1;
 H2 := H2^g2;
 one_W1b := A_101!(one_W1b*g1);
 assert forall{i : i in [1..26] |one_W2b*(A_101!W2.i) eq W2.i};
 W1 := W1*g1;
 assert forall{i : i in [1..26] |one_W1b*(A_101!W1.i) eq W1.i};
 W2 := W2*g2;
 one_W2b := A_101!(one_W2b*g2);
 assert forall{i : i in [1..26] |one_W2b*(A_101!W2.i) eq W2.i};
 x1 := one_W1b-one_Vb;
 x2 := one_W2b-one_Vb;
 assert x1 in U;
 assert x2 in U;
 // Computation 5.3 : This is the longest calculation in the project. My laptop cannot run this

 time Ualg := Algebra< F, 18 | AllStructureConstants(FindStructureConstantsSubalgebra(A_101, U))>;
 time bool, form_U := HasFrobeniusForm(Ualg);
 assert bool;
 assert Dimension(form_U) eq 1;
 // This shows that up to scaling, U hadmits a unique form. We will scale so that it coincides with the form from $A_{101}$/$A_{286}$
 form_U := RestrictedForm(form_101, U);

 // If you have enough ram, then one can run the following:
 // time idemps_276_35 := FindAllIdempotents(Ualg, VectorSapce(Ualg) : length := 276/35, form := form_U);
 // However, the following form of the ideal has been set up with the Groebner basis computed already and
 // works well even on laptops without much memory usage (less than 500 mb.)
   I := eval Read("IDEAL");
   time var := Variety(I);
   time assert VarietySizeOverAlgebraicClosure(I) eq 2;
   // Note that this of course is dependent on the groups that are produced based on the seed, the purpose here is to
   // verify the assertion.
   
 assert #var eq 2;
 x1_s := Ualg!(x1@@BasisMatrix(U));
 assert IsIdempotent(x1_s);
 assert LengthOfElement(x1_s, form_U) eq 276/35;
 x2_s := Ualg!(x2@@BasisMatrix(U));
 assert IsIdempotent(x2_s);
 assert LengthOfElement(x2_s, form_U) eq 276/35;

 W := Subalgebra({@x1_s, x2_s@});
 exists(c_invs){ x : x  in invs_S | not  x[3] in E};
 assert H1^c_invs[3] eq H2;
 assert H2^c_invs[3] eq H1;

 // Computation 5.4
 A_1x1 := Eigenspace(AdMat(x1), 1);
 A_1x2 := Eigenspace(AdMat(x2), 1);
 assert Dimension(A_1x1) eq 4;
 assert Dimension(A_1x2) eq 4;
 assert Dimension(A_1x2 meet U) eq 4;
 assert Dimension(A_1x1 meet U) eq 4;
 // This shows that $(A_{101})_1(x_i)$ is $U_1(x_i)$.  

 U_1x1 := A_1x1@@BasisMatrix(U);
 U_1x2 := A_1x2@@BasisMatrix(U);
 assert forall{v : v in Basis(U_1x1) |x1_s*(Ualg!v) eq v};
 assert forall{v : v in Basis(U_1x2) |x2_s*(Ualg!v) eq v};

 // We denote $W'$ in the paper by W_p 
 W_p := U_1x1 meet U_1x2;
 assert Dimension(W_p) eq 1;
 
 // Computation 5.5 
 // Part (a)
 time idempsW_p := FindAllIdempotents(Ualg, W_p);
 assert #idempsW_p eq 2;
 assert #{x :  x in idempsW_p | x ne 0 } eq 1;
 assert exists(x){x : x in idempsW_p | x ne 0};
 assert LengthOfElement(x, form_U) eq 20/7;

 ad_x := AdMat(x);
 // Computation 5.5 (b)
 assert Eigenvalues(ad_x) eq {<1,1>, <0,5>, <1/14, 6>, <2/7, 2>, <3/7,4>};
 
 // Part (c)
  time fus_law := FindFusionLaw(x);
 assert exists{ i : i in [1..#fus_law] | fus_law[i] eq  [*< 0, 1/14>, [1/14] *] };
 assert exists{ i : i in [1..#fus_law] | fus_law[i] eq  [*< 0, 2/7>, [2/7] *] };
 assert exists{ i : i in [1..#fus_law] | fus_law[i] eq  [*< 0, 3/7>, [3/7] *] };
 // Shows that for $\lambda ne 1$, $0\star \lambda \subseteq \{\lambda \}$, so Seress

 // Computation 5.5 (d)
 assert W eq &+[Eigenspace(ad_x, l) : l in [1,0]]; 
 
 // Computation 5.6 
 T := Eigenspace(ad_x, 1/14);
 assert Subalgebra({@ Ualg!T.i : i in [1..6] @}) eq VectorSpace(Ualg);

 // Remark 5.7
 rhos := Class(S, c_invs[3]);

 rho_rest := {@ RestrictMapToSubspace(Matrix(y), U) : y in rhos @};
 assert #rho_rest eq 1;
 rho := rho_rest[1];
 
 // Computation 5.8
 assert Dimension(W) eq 6;
 time bool, ext_W_T := ExtendAutToMod(Ualg, W, T, IdentityMatrix(F, 6));
 assert bool;
 assert Dimension(ext_W_T) eq 2;
 phi_1 := Matrix(F, 6, 6, Eltseq(ext_W_T.1));
 assert IsIdentity(phi_1);
 phi_2 := Matrix(F, 6, 6, Eltseq(ext_W_T.2));
 assert not IsIdentity(phi_2);
 
 // Computation 5.8 (b)
 min_pol := MinimalPolynomial(phi_2);
 assert Degree(min_pol) eq 2;
 assert IsIrreducible(min_pol);
 Dis := Discriminant(min_pol);
 num := Numerator(AbsoluteValue(Dis));
 den := Denominator(AbsoluteValue(Dis));
 d := LCM(num, den);
 QQ := QuadraticField(-d);

 // Computation 5.9 
 // Part (a)
 roots := Roots( ChangeRing(min_pol, QQ));
 assert #roots eq 2;
 // So the minimal polynomial is separable over the quadratic extension
 assert not IsReal(roots[1][1]-roots[2][1]);
 // thus the real parts are the same
 assert IsReal(roots[1][1]+roots[2][1]);
 // Thus complex parts are negatives of each other, so these two give that the roots are conjugate
 phi_2c := ChangeRing(phi_2, QQ);
 phi_2cmap := MapFromMatrix(phi_2c, ChangeRing(T, QQ));
 T1 := EigenspaceOfMap(phi_2c, ChangeRing(T, QQ),roots[1][1]);
 T2 := EigenspaceOfMap(phi_2c, ChangeRing(T, QQ),roots[2][1]);
 assert forall{ T : T in [T1, T2] | Dimension(T) eq 3};
 assert forall{v : v in Basis(T1) | v@phi_2cmap eq roots[1][1]*v};
 assert forall{v : v in Basis(T2) | v@phi_2cmap eq roots[2][1]*v};

 // Computation 5.9 (b)

 WW := ChangeRing(W, QQ);
 UUalg := ChangeRing(Ualg, QQ);
 time bool, ext_W_T1 := ExtendAutToMod(UUalg, WW, T1, IdentityMatrix(QQ, 6)); 
 assert bool;
 assert Dimension(ext_W_T1) eq 1;
 time bool, ext_W_T2 := ExtendAutToMod(UUalg, WW, T2, IdentityMatrix(QQ, 6)); 
 assert bool;
 assert Dimension(ext_W_T2) eq 1;

 // Computation 5.10 
 w1 := UUalg!T1.1;
 w2 := UUalg!T2.1;
 assert w1 ne 0 and w2 ne 0;
 w := UUalg!WW.1;
 assert FrobeniusFormAtElements(w1*w1*w1, w, form_U) ne 0;
 assert FrobeniusFormAtElements(w2*w2*w2, w, form_U) ne 0;
 
 // Computation 5.12
 rho_QQ := ChangeRing(rho, QQ);
 assert T1*rho_QQ eq T2;
 assert T2*rho_QQ eq T1;
 
 // We now set up Computation 5.14
 W1 := decomps[[0, 1/32, 1/32]];
 W2 := decomps[[1/32, 0, 1/32]];
 W3 := decomps[[1/32, 1/32, 0]];

 // Computation 5.14 (a)
 assert Dimension(Subalgebra(&join[{@A_101!W.i :  i in [1..Dimension(W)] @} : W in [W1, W2]])) eq 101;
 assert Dimension(Subalgebra(&join[{@A_101!W.i :  i in [1..Dimension(W)] @} : W in [W1, W3]])) eq 101;
 assert Dimension(Subalgebra(&join[{@A_101!W.i :  i in [1..Dimension(W)] @} : W in [W2, W3]])) eq 101;
 // We have shown in fact, that any two $W_i$s generata $A=A_{101}$ so hence the three
 //assert Order(rho) eq 2;
 
 // Computaion 5.14 (b)
 time bool, ext_U_W1 := ExtendAutToMod(A_101, U, W1, IdentityMatrix(F, 18));
 assert bool;
 assert Dimension(ext_U_W1) eq 1;
 time bool, ext_U_W2 := ExtendAutToMod(A_101, U, W2, IdentityMatrix(F, 18));
 assert bool;
 assert Dimension(ext_U_W2) eq 1;
 time bool, ext_U_W3 := ExtendAutToMod(A_101, U, W3, IdentityMatrix(F, 18));
 assert bool;
 assert Dimension(ext_U_W3) eq 1;
 rests := [RestrictMapToSubspace(Matrix(x), U): x in S | x notin E]; 
 #rests;
 assert #Set(rests) eq 1;

 // Computation 5.14 (c)
 w1 := A_101!W1.1;
 w2 := A_101!W2.1;
 w3 := A_101!W3.1;
 u := A_101!U.1;
 // Part (i)
 assert FrobeniusFormAtElements(w1*w1, u, form_101) ne 0;
 assert FrobeniusFormAtElements(w2*w2, u, form_101) ne 0;
 assert FrobeniusFormAtElements(w3*w3, u, form_101) ne 0;
 assert FrobeniusFormAtElements(w1*w2, w3, form_101) ne 0;
 rho in rests;
 NN := Normaliser(G, E);
 assert exists(x_out){x : x in NN | x notin N}; 
 assert Order(x_out) eq 2;
 xx_out := RestrictMapToSubspace(Matrix(x_out), U);
 assert rho ne xx_out;
 H := MatrixGroup<18, F| rho, xx_out>;
 assert Order(rho*xx_out) eq 3;
 assert #{xx_out, rho,(rho*xx_out)^-1*rho*(rho*xx_out)} eq 3;
 invs_H := [rho, xx_out, Matrix((H!rho)^(H!(rho*xx_out)))];
 assert #Set(invs_H) eq 3;
 assert forall{x : x in invs_H | Order(x) eq 2};
 
// Computation 5.16 (a)
 exts_1 := [bool where bool,_ := ExtendAutToMod(A_101, U, W, invs_H[1]) : W in [W1, W2, W3]]; 
 assert #{i : i in [1..3] | exts_1[i] eq true} eq 1;
 time exts_2 := [bool where bool,_ := ExtendAutToMod(A_101, U, W, invs_H[2]) : W in [W1, W2, W3]]; 
 assert #{i : i in [1..3] | exts_2[i] eq true} eq 1;
 time exts_3 := [bool where bool,_ := ExtendAutToMod(A_101, U, W, invs_H[3]) : W in [W1, W2, W3]]; 
 assert #{i : i in [1..3] | exts_3[i] eq true} eq 1;

 // Computation 5.16 (b)
 //assert Order(xx_out*rho) eq 3;
 time exts_ord_3 := [bool where bool,_ := ExtendAutToMod(A_101, U, W, invs_H[1]*invs_H[2]) : W in [W1, W2, W3]]; 
 //time exts_ord_3 := [bool where bool,_ := ExtendAutToMod(A_101, U, W, invs_H[1]*invs_H[2]) : W in [W1, W2, W3]]; 
 assert forall{i : i in [1..3] |exts_ord_3[i] eq false};
 time exts_ord_3 := [bool where bool,_ := ExtendAutToMod(A_101, U, W, invs_H[2]*invs_H[1]) : W in [W1, W2, W3]]; 
 assert forall{i : i in [1..3] |exts_ord_3[i] eq false};
 assert invs_H[1]*invs_H[2] ne invs_H[2]*invs_H[1];
 assert forall{ x : x in [invs_H[1]*invs_H[2] , invs_H[2]*invs_H[1]] | Order(x) eq 3 };
 assert #{invs_H[1]*invs_H[2] , invs_H[2]*invs_H[1]} eq 2;
 // Thus these are all the 3-elements in H
