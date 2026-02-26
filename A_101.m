 SetSeed(1);
 Attach("Automorphisms.m");
 SetVerbose("Automorphisms", 1); 
 F := Rationals();
 time A_101 := eval Read("A_101");
  time bool, form_101v := HasFrobeniusForm(A_101);
 assert bool;

 // Computation 5.1 (d)
 assert Dimension(form_101v) eq 1; 
 form_101 := eval Read("form_101");
 axes_101 := [A_101.i : i in [1..101] | IsIdempotent(A_101.i)];
 time Miy101_p, Miy101, isom101, gpname101 := MiyamotoGroup(axes_101);
 time G_perm, G, iso_G, gpname_G, _ := GroupFromAxes(axes_101);
 assert gpname_G eq "PSL(2,11).C2";
 S := SylowSubgroup(G, 2);
 assert GroupName(S) eq "D4";
 assert Order(S) eq 8;
 invs_S := [x : x in ConjugacyClasses(S) | x[1] eq 2];
 assert #invs_S eq 3;
 exists(cent){ x : x in invs_S | x[2] eq 1};
 tau_1 := cent[3];
 
 time IsInducedFromAxis(A_101, Matrix(tau_1):automorphism_check := false, form := form_101);
 // Better to use the following
 _, a1 :=$1;

 a_1 := a1[1];
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
 Y := {@a_1, a_2, a_3 @};
 assert exists(tau_3){x : x in Class(S, tau_2) | x ne tau_2};
 E := sub< S | tau_1, tau_2, tau_3>;
 assert GroupName(E) eq "C2^2";

 // Computation 5.1 (a)
 time jordans := JordanAxes(A_101, [Matrix(x) : x in Generators(Miy101)]: form := form_101);

 assert IsEmpty(jordans);
 // Computation 5.1 (b)
 time twins := FindTwins(axes_101[1]: form := form_101);
 assert IsEmpty(twins);
 // Computation 5.1 (c)
 invs_G := [x : x in ConjugacyClasses(G) | x[1] eq 2];
 assert #invs_G eq 2;
 G0 := Miy101;
 exists(c_2A){x : x in invs_G | x[3] in G0};
 assert c_2A[2] eq 55;
 assert exists(c_2B){x : x in invs_G | not x[3] in G0};
 bool,_ := IsInducedFromAxis(A_101, Matrix(c_2B[3]): form := form_101, automorphism_check := false);
 assert not bool;
 // Setup for 5.2 onwards
 N0 := Normaliser(G0, E);
 assert GroupName(N0) eq "A4";
 N := Normaliser(G, E);
 assert GroupName(N) eq "S4";
 subs_60 := Subgroups(G0: OrderEqual := 60);
 assert #subs_60 eq 2;
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
 //V_alg := Algebra<F, 3| AllStructureConstants(FindStructureConstantsSubalgebra(A_101, V))>;
 W1_alg := Algebra<F, 26| AllStructureConstants(FindStructureConstantsSubalgebra(A_101, W1))>;
 W2_alg := Algebra<F, 26| AllStructureConstants(FindStructureConstantsSubalgebra(A_101, W2))>;
 _,one_W1 := HasOne(W1_alg); 
 _,one_W2 := HasOne(W2_alg); 
 one_Vb := 4/5*(&+Y);
 assert forall{y: y in Y |one_Vb*y eq y};
 one_W1b := A_101!(one_W1@BasisMatrix(W1));
 assert forall{i : i in [1..26] |one_W1b*(A_101!W1.i) eq W1.i};
 one_W2b := A_101!(one_W2@BasisMatrix(W2));
 assert forall{i : i in [1..26] |one_W2b*(A_101!W2.i) eq W2.i};
 assert exists(g1){g : g in G0| N0 subset H1^g };
 assert exists(g2){g : g in G0| N0 subset H2^g };
 H1 := H1^g1;
 H2 := H2^g2;
 one_B1b := A_101!(one_W1b*g1);
 one_B2b := A_101!(one_W2b*g2);
 B1 := W1*g1;
 B2 := W2*g2;
 assert forall{i : i in [1..26] |one_B1b*(A_101!B1.i) eq B1.i};
 assert forall{i : i in [1..26] |one_B2b*(A_101!B2.i) eq B2.i};
 b1 := one_B1b-one_Vb;
 b2 := one_B2b-one_Vb;
 assert b1 in U;
 assert b2 in U;
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
   time Groebner(I);
   time var := Variety(I);
   time assert VarietySizeOverAlgebraicClosure(I) eq 2;
   // Note that this of course is dependent on the groups that are produced based on the seed, the purpose here is to
   // verify the assertion.
   
 assert #var eq 2;
 b1_s := Ualg!(b1@@BasisMatrix(U));
 assert IsIdempotent(b1_s);
 assert LengthOfElement(b1_s, form_U) eq 276/35;
 b2_s := Ualg!(b2@@BasisMatrix(U));
 assert IsIdempotent(b2_s);
 assert LengthOfElement(b2_s, form_U) eq 276/35;

 W := Subalgebra({@b1_s, b2_s@});
 assert Dimension(W) eq 6;
 assert exists(c_invs){ x : x  in invs_S | x[3] notin E};
 assert H1^c_invs[3] eq H2;
 assert H2^c_invs[3] eq H1;

 // Computation 5.4
 //Part (a)
 A_1b1 := Eigenspace(AdMat(b1), 1);
 A_1b2 := Eigenspace(AdMat(b2), 1);
 assert Dimension(A_1b1) eq 4;
 assert Dimension(A_1b2) eq 4;
 assert Dimension(A_1b2 meet U) eq 4;
 assert Dimension(A_1b1 meet U) eq 4;
 // This shows that $(A_{101})_1(b_i)$ is $U_1(b_i)$.  

 U_1b1 := A_1b1@@BasisMatrix(U);
 U_1b2 := A_1b2@@BasisMatrix(U);
 assert forall{v : v in Basis(U_1b1) | b1_s*(Ualg!v) eq v};
 assert forall{v : v in Basis(U_1b2) | b2_s*(Ualg!v) eq v};

 // We denote $W'$ in the paper by W_p 
 W_p := U_1b1 meet U_1b2;
 assert Dimension(W_p) eq 1;
 
 // Part (b)
 time idempsW_p := FindAllIdempotents(Ualg, W_p);
 assert #idempsW_p eq 2;
 assert exists(x){x : x in idempsW_p | x ne 0};
 assert LengthOfElement(x, form_U) eq 20/7;

 ad_x := AdMat(x);
 // Computation 5.4 (c)
 assert Eigenvalues(ad_x) eq {<1,1>, <0,5>, <1/14, 6>, <2/7, 2>, <3/7,4>};
 
 // Part (d)
  time fus_law := FindFusionLaw(x);
 assert exists{ i : i in [1..#fus_law] | fus_law[i] eq  [*< 0, 1/14>, [1/14] *] };
 assert exists{ i : i in [1..#fus_law] | fus_law[i] eq  [*< 0, 2/7>, [2/7] *] };
 assert exists{ i : i in [1..#fus_law] | fus_law[i] eq  [*< 0, 3/7>, [3/7] *] };
 // Shows that for $\lambda ne 1$, $0\star \lambda \subseteq \{\lambda \}$, so Seress

 // Computation 5.4 (e)
 assert W eq &+[Eigenspace(ad_x, l) : l in [1,0]]; 
 
 // Computation 5.5 
 T := Eigenspace(ad_x, 1/14);
 assert Subalgebra({@ Ualg!T.i : i in [1..6] @}) eq VectorSpace(Ualg);

 // Computation 5.6 
 //Part (a)
 time bool, ext_W_T := ExtendAutToMod(Ualg, W, T, IdentityMatrix(F, 6));
 assert bool;
 assert Dimension(ext_W_T) eq 2;
 phi_1 := Matrix(F, 6, 6, Eltseq(ext_W_T.1));
 assert IsIdentity(phi_1);
 phi_2 := Matrix(F, 6, 6, Eltseq(ext_W_T.2));
 assert not IsIdentity(phi_2);
 
 // Computation 5.6 (b)
 min_pol := MinimalPolynomial(phi_2);
 assert Degree(min_pol) eq 2;
 assert IsIrreducible(min_pol);
 Dis := Discriminant(min_pol);
 num := Numerator(AbsoluteValue(Dis));
 den := Denominator(AbsoluteValue(Dis));
 d := LCM(num, den);
 QQ := QuadraticField(-d);
 // turns out that the field is actually the cylotomic extension of $\mathbb(Q)$ by a primitive cube root of unity
 FF := CyclotomicField(3);
 assert IsCoercible(FF, QQ.1);
 // Computation 5.7 
 // Part (a)
 roots := Roots(ChangeRing(min_pol, FF));
 assert #roots eq 2;
 // So the the quadratic extension is separable 
 assert not IsReal(roots[1][1]-roots[2][1]);
 // thus the real parts are the same
 assert IsReal(roots[1][1]+roots[2][1]);
 // Thus complex parts are negatives of each other, so these two give that the roots are conjugate
 phi_2c := ChangeRing(phi_2, FF);
 phi_2cmap := MapFromMatrix(phi_2c, ChangeRing(T, FF));
 T1 := EigenspaceOfMap(phi_2c, ChangeRing(T, FF),roots[1][1]);
 T2 := EigenspaceOfMap(phi_2c, ChangeRing(T, FF),roots[2][1]);
 assert forall{T : T in [T1, T2] | Dimension(T) eq 3};
 assert forall{v : v in Basis(T1) | v@phi_2cmap eq roots[1][1]*v};
 assert forall{v : v in Basis(T2) | v@phi_2cmap eq roots[2][1]*v};

 // Computation 5.7 (b)
 WW := ChangeRing(W, FF);
 UUalg := ChangeRing(Ualg, FF);
 assert forall{v : v in Basis(T1) | forall{w : w in Basis(WW) | (UUalg!v)*(UUalg!w) in T1}};  
 assert forall{v : v in Basis(T2) | forall{w : w in Basis(WW) | (UUalg!v)*(UUalg!w) in T2}}; 

 // Part (c)
 time bool, ext_W_T1 := ExtendAutToMod(UUalg, WW, T1, IdentityMatrix(FF, 6)); 
 assert bool;
 assert Dimension(ext_W_T1) eq 1;
 time bool, ext_W_T2 := ExtendAutToMod(UUalg, WW, T2, IdentityMatrix(FF, 6)); 
 assert bool;
 assert Dimension(ext_W_T2) eq 1;

 // Computation 5.8 
 t1 := UUalg!T1.1;
 t2 := UUalg!T2.1;
 assert t1 ne 0 and t2 ne 0;
 w := UUalg!WW.1;
 // Part (a)
 assert FrobeniusFormAtElements(t1*t1*t1, w, form_U) ne 0;
 assert FrobeniusFormAtElements(t2*t2*t2, w, form_U) ne 0;
 // Part (b)
 assert FrobeniusFormAtElements(t1*t2, w, form_U) ne 0;
 
 // We now set up Computation 5.11
 W1 := decomps[[0, 1/32, 1/32]];
 W2 := decomps[[1/32, 0, 1/32]];
 W3 := decomps[[1/32, 1/32, 0]];

 // Computation 5.11 (a)
 assert Dimension(Subalgebra(&join[{@A_101!W.i :  i in [1..Dimension(W)] @} : W in [W1, W2]])) eq 101;
 assert Dimension(Subalgebra(&join[{@A_101!W.i :  i in [1..Dimension(W)] @} : W in [W1, W3]])) eq 101;
 assert Dimension(Subalgebra(&join[{@A_101!W.i :  i in [1..Dimension(W)] @} : W in [W2, W3]])) eq 101;
 // We have shown in fact, that any two $W_i$s generat $A=A_{101}$ so hence the three
 
 // Computaion 5.11 (b)
 time bool, ext_U_W1 := ExtendAutToMod(A_101, U, W1, IdentityMatrix(F, 18));
 assert bool;
 assert Dimension(ext_U_W1) eq 1;
 time bool, ext_U_W2 := ExtendAutToMod(A_101, U, W2, IdentityMatrix(F, 18));
 assert bool;
 assert Dimension(ext_U_W2) eq 1;
 time bool, ext_U_W3 := ExtendAutToMod(A_101, U, W3, IdentityMatrix(F, 18));
 assert bool;
 assert Dimension(ext_U_W3) eq 1;

 // Computation 5.11 (c)
 w1 := A_101!W1.1;
 w2 := A_101!W2.1;
 w3 := A_101!W3.1;
 u := A_101!U.1;
 // Part (i)
 assert FrobeniusFormAtElements(w1*w1, u, form_101) ne 0;
 assert FrobeniusFormAtElements(w2*w2, u, form_101) ne 0;
 assert FrobeniusFormAtElements(w3*w3, u, form_101) ne 0;
 // Part (ii)
 assert FrobeniusFormAtElements(w1*w2, w3, form_101) ne 0;
