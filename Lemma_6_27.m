 F := Rationals();
 G := Group("M11");
 irr := IrreducibleModules(G, GF(3));
 assert #irr eq 8;
 assert Dimension(irr[3]) eq 5;
 P := SplitExtension(GrpPerm, G, irr[2]);
 invs_P := [ x : x in Classes(P) | x[1] eq 2];
 assert #invs_P eq 1;
 D := invs_P[1][3]^P;
 load "~/Computations/IsSixTranspositionClass.m";// add this file to the folder and change this part
 time assert IsMTranspositionGroup(6, D, P);
 assert NumberOfGenerators(P) eq 12;
 H := sub<P | [P.i : i in [1..7]]>;
 assert GroupName(H) eq "M11";
 invs_H := [ x : x in Classes(H) | x[1] eq 2];
 assert #invs_H eq 1;
 X := invs_H[1][3]^H;
 time Y := GSet(P, Subsets(Set(D),2));
 orbs := Orbits(P,Y);
 assert #orbs eq 9;
 YY := {y : y in Y | y subset Set(X)};
 closures := [];
 for i := 1 to #orbs do
    o := orbs[i];
    o_r := o[1];
    Dihed := sub<P | o_r>;
    o_seq := SetToSequence(o_r);
    clos := &join{o_seq[i]^Dihed: i in [1,2]};;
    Append(~closures, clos);
 end for;
 [#x : x in closures ]; 
 // We could have just found the orders of the products
 assert [#x : x in closures] eq [Order(&*orbs[i][1]) : i in [1..9]];
 shapes := [];
 sixes := [i :i in [1..9] | #closures[i] eq 6];
 assert #sixes eq 2;
 for x in sixes do
    shapes[x] := "6A";
 end for;
 // There are no choices for 6X.
 fives := [i : i in [1..9] | #closures[i] eq 5 ];
 assert #fives eq 1;
 shapes[fives[1]] := "5A";
 // again there are no choices for 5X
 for i in {1..9} diff Set(fives cat sixes) do
    o := orbs[i];
    o_r := o[1];
    if o_r in YY then 
       if #closures[i] eq 2 then
          shapes[i] := "2A";
       elif #closures[i] eq 3 then
          shapes[i] := "3A";
       elif #closures[i] eq 4 then
          shapes[i] := "4B";
       end if;
    elif exists(g){ g : g in P | o_r^g in YY} then
       assert exists(orb){ x : x in orbs | o_r^g in x};
       j := Index(orbs, orb);
       if #closures[j] eq 2 then
          shapes[j] := "2A";
       elif #closures[j] eq 3 then
          shapes[j] := "3A";
       elif #closures[j] eq 4 then
          shapes[j] := "4B";
       end if;
    end if;
 end for;
 undefined := [i : i in [1..9] | not IsDefined(shapes, i)];
 assert #undefined eq 2;
 // Thus, we only have 4 choices of shapes
 assert forall{x : x in undefined | #closures[x] eq 3};
 // Thus we have two orbits with possible choices of 3A or 3C
 shape1 := shapes;
 shape1[undefined[1]] := "3A";
 shape1[undefined[2]] := "3A";
 shape1;
 shape2 := shapes;
 shape2[undefined[1]] := "3C";
 shape2[undefined[2]] := "3A";
 shape2;
 shape3 := shapes;
 shape3[undefined[1]] := "3A";
 shape3[undefined[2]] := "3C";
 assert #{shape1, shape2, shape3} eq 3;
 shape4 := shapes;
 shape4[undefined[1]] := "3C";
 shape4[undefined[2]] := "3C";
 assert #{shape1, shape2, shape3,shape4} eq 4;
 // set up an associative array for angles
 frobenius_angles := AssociativeArray();
 frobenius_angles["1A"] := 1;
 frobenius_angles["2A"] := 1/8;
 frobenius_angles["2B"] := 0;
 frobenius_angles["3A"] := 13/(2^8);
 frobenius_angles["3C"] := 1/(2^6);
 frobenius_angles["4A"] := 1/(2^5);
 frobenius_angles["4B"] := 1/(2^6);
 frobenius_angles["5A"] := 3/(2^7);
 frobenius_angles["6A"] := 5/(2^8);

 // Gram matrix for shape 1
 L1 := [F | ];
 for i :=1 to #D do
    for j := 1 to #D do
       if i eq j then 
          Append(~L1, 1);
       else
          pair := {D[i], D[j]};
          assert exists(orb){x : x in orbs | pair in x};
          ind := Index(orbs, orb);
          Append(~L1, frobenius_angles[shape1[ind]]);
       end if;
    end for;
 end for;
 gram1 := Matrix(#D, #D, L1);
 assert Rank(gram1) eq 1485;

 // Gram matrix for shape 2
 L2 := [F | ];
 for i :=1 to #D do
    for j := 1 to #D do
       if i eq j then 
          Append(~L2, 1);
          else
          pair := {D[i], D[j]};
          assert exists(orb){x : x in orbs | pair in x};
          ind := Index(orbs, orb);
          Append(~L2, frobenius_angles[shape2[ind]]);
       end if;
    end for;
 end for;
 gram2 := Matrix(#D, #D, L2);
 assert Rank(gram2) eq 1485;

 // third shape
 L3 := [F | ];
 for i :=1 to #D do
    for j := 1 to #D do
       if i eq j then 
          Append(~L3, 1);
       else
          pair := {D[i], D[j]};
          assert exists(orb){x : x in orbs | pair in x};
          ind := Index(orbs, orb);
          Append(~L3, frobenius_angles[shape3[ind]]);
       end if;
    end for;
 end for;
 gram3 := Matrix(#D, #D, L3);
 assert #{gram1, gram2, gram3} eq 3;
 assert Rank(gram3) eq 1430;

 // Gram matrix for shape 4
 L4 := [F | ];
 for i :=1 to #D do
    for j := 1 to #D do
       if i eq j then 
          Append(~L4, 1);
       else
          pair := {D[i], D[j]};
          assert exists(orb){x : x in orbs | pair in x};
          ind := Index(orbs, orb);
          Append(~L4, frobenius_angles[shape4[ind]]);
       end if;
    end for;
 end for;
 gram4 := Matrix(#D, #D, L4);
 assert Rank(gram4) eq 1485;
 
 // Computations for the second 5-dim module
 P2 := SplitExtension(GrpPerm, G, irr[3]);
 invs_P2 := [x : x in Classes(P2) | x[1] eq 2];
 D2 := invs_P2[1][3]^P2;;
 time assert IsMTranspositionGroup(6, D2, P2);
 time Y2 := GSet(P2, Subsets(Set(D2), 2));
 time orbs2 := Orbits(P2, Y2);
 H2 := sub<P2 | [P2.i : i in [1..7]]>;
 assert GroupName(H2) eq "M11";
 invs_H2 := [x : x in Classes(H2) | x[1] eq 2];
 X2 := invs_H2[1][3]^H2;
 time YY2 := {y : y in Y2 | y subset Set(X2)};
 closures2 := [Order(&*(orbs2[i][1])) : i in [1..9]];
 closures2;

 // first we deal with the 5X and 6X cases with no choice as usual
 shapes2 := [];
 sixes2 := [i : i in [1..9] | closures2[i] eq 6];
 assert #sixes2 eq 2;
 for x in sixes2 do
    shapes2[x] := "6A";
 end for;
 shapes2;
 fives2 := [i : i in [1..9] | closures2[i] eq 5];
 assert #fives2 eq 1;
 shapes2[fives2[1]] := "5A";
 shapes2;
 // We now consider the orbits which conjugate with pairs in M_11
 
 shapes2;
  for i in {1..9} diff Set(fives2 cat sixes2) do
    o := orbs2[i];
    o_r := o[1];
    if o_r in YY2 then
       if closures2[i] eq 2 then
          shapes2[i] := "2A";
          elif closures2[i] eq 3 then
          shapes2[i] := "3A";
          elif closures2[i] eq 4 then
          shapes2[i] := "4B";
       end if;
    elif exists(g){g : g in P2 | o_r^g in YY2} then
       assert exists(orb){x : x in orbs2 | o_r^g in x};
       j := Index(orbs2, orb);
       if closures2[j] eq 2 then
          shapes2[j] := "2A";
          elif closures2[j] eq 3 then
          shapes2[j] := "3A";
          elif closures2[j] eq 4 then
          shapes2[j] := "4B";
          end if;
       end if;
    end for;
 shapes2;
 // again we actually have four choices for the shape
 undefined2 := [i : i in [1..9] | not IsDefined(shapes2, i)];
 assert #undefined2 eq 2;
 // again we have choices of 3A or 3C in two orbits
 assert forall{ x : x in undefined2 | closures2[x] eq 3}; 
 shape1a := shapes2;
 shape1a[undefined2[1]] := "3A";
 shape1a[undefined2[2]] := "3A";
 shape2a := shapes2;
 shape2a[undefined2[1]] := "3A";
 shape2a[undefined2[2]] := "3C";
 shape2a;
 #{shape1a, shape2a};
 shape3a := shapes2;
 shape3a[undefined2[1]] := "3C";
 shape3a[undefined2[2]] := "3A";
 shape3a;
 assert #{shape1a, shape2a, shape3a} eq 3;
 shape4a := shapes2;
 shape4a[undefined2[1]] := "3C";
 shape4a[undefined2[2]] := "3C";
 shape4a;
 assert #{shape1a, shape2a, shape3a, shape4a} eq 4;
 // Now we deal with the gram matrices
 
 // shape 1
 LL1 := [F | ];
 for i := 1 to #D2 do
    for j := 1 to #D2 do
       if i eq j then
          Append(~LL1, 1); 
       else
          pair := {D2[i], D2[j]};
          assert exists(orb){x : x in orbs2 | pair in x};
          ind := Index(orbs2, orb);
          Append(~LL1, frobenius_angles[shape1a[ind]]);
       end if;
    end for;
 end for;
 gram1a := Matrix(#D2, #D2, LL1);
 Rank(gram1a);
 
 // shape 2
 LL2 := [F | ];
 for i := 1 to #D2 do
    for j := 1 to #D2 do
       if i eq j then
          Append(~LL2, 1); 
       else
          pair := {D2[i], D2[j]};
          assert exists(orb){x : x in orbs2 | pair in x};
          ind := Index(orbs2, orb);
          Append(~LL2, frobenius_angles[shape2a[ind]]);
       end if;
    end for;
 end for;
 gram2a := Matrix(#D2, #D2, LL2);
 Rank(gram2a);

 //shape 3
 LL3 := [F | ];
 for i := 1 to #D2 do
    for j := 1 to #D2 do
       if i eq j then
          Append(~LL3, 1); 
       else
          pair := {D2[i], D2[j]};
          assert exists(orb){x : x in orbs2 | pair in x};
          ind := Index(orbs2, orb);
          Append(~LL3, frobenius_angles[shape3a[ind]]);
       end if;
    end for;
 end for;
 gram3a := Matrix(#D2, #D2, LL3);
 Rank(gram3a);
 
 // shape 4
 LL4 := [F | ];
 for i := 1 to #D2 do
    for j := 1 to #D2 do
       if i eq j then
          Append(~LL4, 1); 
       else
          pair := {D2[i], D2[j]};
          assert exists(orb){x : x in orbs2 | pair in x};
          ind := Index(orbs2, orb);
          Append(~LL4, frobenius_angles[shape4a[ind]]);
       end if;
    end for;
 end for;
 gram4a := Matrix(#D2, #D2, LL4);
 Rank(gram4a);
 // so we have two Gram matrices of full rank and two defective ones of ranks 1265 and 1386
 ranks := [Rank(m) : m in [gram1a, gram2a, gram3a, gram4a]];
 assert Set(ranks) eq {1485, 1386, 1265};

// The first module of dimension 10
 P3 := SplitExtension(GrpPerm, G, irr[4]);
 invs_P3 := [x : x in ConjugacyClasses(P3) | x[1] eq 2];
 assert #invs_P3 eq 1;
 D3 := invs_P3[1][3]^P3;
 assert not IsMTranspositionClass(6, D3, P3); // we could also use IsMTranspositionGroup but they are equivalent since one class 
// The second module of dimension 10
 P4 := SplitExtension(GrpPerm, G, irr[5]);
 invs_P4 := [x : x in ConjugacyClasses(P4) | x[1] eq 2];
 assert #invs_P4 eq 1;
 D4 := invs_P4[1][3]^P4;
 assert not IsMTranspositionClass(6, D4, P4);
					     
// The third module of dimension 10
 P5 := SplitExtension(GrpPerm, G, irr[6]);
 invs_P5 := [x : x in ConjugacyClasses(P5) | x[1] eq 2];
 assert #invs_P5 eq 1;
 D5 := invs_P5[1][3]^P5;
 assert not IsMTranspositionClass(6, D5, P5);

 // Module of dimension 24
 // The normal algorithms will not work to get classes. We got a custom construction 
 // from E. O'brien whose help is gratefully acknowledged.
 
 SetGlobalTCParameters(: Hard, CosetLimit := 10^9, Print := 10^6);
 P6 := SplitExtension(GrpPerm, G, irr[7]);
 assert Ngens(P6) eq 31;
 n_gens := Ngens(P6);
 printf("The number of generators of P6 is %o.\n"), n_gens; 
 H6 := sub<P6 | [P6.i : i in [1..7]]>;
 assert GroupName(H6) eq "M11";
 N6 := sub<P6 | [P6.i : i in [8..n_gens]] >;
 assert IsElementaryAbelian(N6);
 invs_H6 := [x : x in Classes(H6) | x[1] eq 2];
 assert #invs_H6 eq 1;
 h6 := invs_H6[1][3];
 Ch6 := Class(H6, h6);
 assert #Ch6 eq 165;
 assert {FactoredOrder(Centraliser(N6, x)) : x in Ch6 } eq {[<3, 12>]};
 CPh6 := Centraliser(P6, h6);
 assert #P6 div #CPh6 eq 165*3^12;
 Ch6 := SetToSequence(Ch6);
 // Since we claim that the class is not a 6-transposition class, we need not produce it all. 
 load "ConstructClass.m";
 Cx6 := ConstructClass(P6, N6, Ch6[5]: Limit := 3^6);
 R6 := Ch6 cat SetToSequence(Cx6);
 assert exists(pair){<x, y> : x, y in R6 | Order(x*y) gt 6};// if this assertion fails try another element in Ch6
 Order(&*pair);
 // Hence in this case P (=P6) is not a 6-transposition group.
 
 // Module of dimension 45
 P7 := SplitExtension(GrpPerm, G, irr[8]);
 assert Ngens(P7) eq 52;
 H7 := sub<P7 | [P7. i : i in [1..7]]>;
 assert GroupName(H7) eq "M11";
 N7 := sub<P7 | [P7.i : i in [8..52]]>;
 assert IsElementaryAbelian(N7);
 invs_H7 := [x : x in Classes(H7) | x[1] eq 2];
 assert #invs_H7 eq 1;
 h7 := invs_H7[1][3];
 Ch7 := Class(H7, h7);
 assert #Ch7 eq 165;
 assert {FactoredOrder(Centraliser(N7, x)) : x in Ch7 } eq {[<3, 21>]};
 CPh7 := Centraliser(P7, h7);
 assert #P7 div #CPh7 eq 165*3^24;
 Ch7 := SetToSequence(Ch7);
 classes := [];
 for i := 1 to 165 do 
    Cxi := ConstructClass(P7, N7, Ch7[i]: Limit := 3^6);
    R := SetToSequence(Cxi) cat Ch7;
    if exists(pair7){<x, y> : x, y in R | Order(&*<x, y>) gt 6} then
       break i;
    else
       Append(~classes, Cxi);
    end if;
 end for;
 Order(&*pair7);
 // If there is a failure then form the join of the classes and search in the enlarged class. 
 // In my run a pair was produced on the first try in less than half minute

 // p =5


 irr5 := IrreducibleModules(G, GF(5));
 assert #irr5 eq 8;
 irr5;
 // Dimension 10
 time P := SplitExtension(GrpPerm, G, irr5[2]);
 assert Ngens(P) eq 17;
 H := sub<P | [P.i : i in [1..7]]>;
 assert GroupName(H) eq "M11";
 N := sub<P | [P.i : i in [8..17]]>;
 assert IsElementaryAbelian(N);
 invs_H := [ x : x in Classes(H) | x[1] eq 2];
 assert #invs_H eq 1;
 h := invs_H[1][3];
 Ch := Class(H, h);
 assert #Ch eq 165;
 CPh := Centraliser(P, h);
 assert {FactoredOrder(Centraliser(N, x)) : x in Ch} eq { [<5, 6>]};
 assert #P div #CPh eq 165*5^4;
 Ch := SetToSequence(Ch);
 classes := [];
 for i := 1 to 165 do
     Cxi := ConstructClass(P, N, Ch[i]: Limit := 5^2);
     R := SetToSequence(Cxi) cat Ch;
     if exists(pair){<x,y> : x, y in R | Order(&*<x,y>) gt 6} then
        break i;
     else
        Append(~classes, Cxi);
     end if;
 end for;
 Order(&*pair);

 // dimension 11
 time P2 := SplitExtension(GrpPerm, G, irr5[3]);
 assert Ngens(P2) eq 18;
 H2 := sub<P2 | [P2.i : i in [1..7]]>;
 assert GroupName(H2) eq "M11";
 N2 := sub<P2 | [P2.i : i in [8..18]]>;
 assert IsElementaryAbelian(N2);
 invs_H2 := [ x : x in Classes(H2) | x[1] eq 2];
 assert #invs_H2 eq 1;
 h2 := invs_H2[1][3];
 Ch2 := Class(H2, h2);
 assert #Ch2 eq 165;
 CPh2 := Centraliser(P2, h2);
 assert {FactoredOrder(Centraliser(N2, x)) : x in Ch2} eq { [<5, 7>]};;
 assert #P2 div #CPh2 eq 165*5^4;
 Ch2 := SetToSequence(Ch2);
 for i := 1 to 165 do
     Cxi := ConstructClass(P2, N2, Ch2[i]: Limit := 5^2);
     R := SetToSequence(Cxi) cat Ch2;
     if exists(pair){<x,y> : x, y in R | Order(&*<x,y>) gt 6} then
        break i;
     else
        [];
     end if;
 end for;
 Order(&*pair);

 // The first 16-dim module]
 time P3 := SplitExtension(GrpPerm, G, irr5[4]);
 assert Ngens(P3) eq 23;
 H3 := sub<P3 | [P3.i : i in [1..7]]>;
 assert GroupName(H3) eq "M11";
 N3 := sub<P3 | [P3.i : i in [8..23]]>;
 assert IsElementaryAbelian(N3);
 invs_H3 := [ x : x in Classes(H3) | x[1] eq 2];
 assert #invs_H3 eq 1;
 h3 := invs_H3[1][3];
 Ch3 := Class(H3, h3);
 assert #Ch3 eq 165;
 CPh3 := Centraliser(P3, h3);
 assert {FactoredOrder(Centraliser(N3, x)) : x in Ch3} eq {[<5, 8> ]};
 assert #P3 div #CPh3 eq 165*5^8;
 Ch3 := SetToSequence(Ch3);
 classes3 := [];
 for i := 1 to 165 do
     Cxi := ConstructClass(P3, N3, Ch3[i]: Limit := 5^4);
     R := SetToSequence(Cxi) cat Ch3;
     if exists(pair){<x,y> : x, y in R | Order(&*<x,y>) gt 6} then
        break i;
     else
        Append(~classes3, Cxi);
     end if;
 end for;

 Order(&*pair);

 // The second 16-dim module]
 time P4 := SplitExtension(GrpPerm, G, irr5[5]);
 assert Ngens(P4) eq 23;
 H4 := sub<P4 | [P4.i : i in [1..7]]>;
 assert GroupName(H4) eq "M11";
 N4 := sub<P4 | [P4.i : i in [8..23]]>;
 assert IsElementaryAbelian(N4);
 invs_H4 := [ x : x in Classes(H4) | x[1] eq 2];
 assert #invs_H4 eq 1;
 h4 := invs_H4[1][3];
 Ch4 := Class(H4, h4);
 assert #Ch4 eq 165;
 CPh4 := Centraliser(P4, h4);
 assert {FactoredOrder(Centraliser(N4, x)) : x in Ch4} eq {[<5, 8> ]};
 classes4 := [];
 Ch4 := SetToSequence(Ch4);
 for i := 1 to 165 do
     Cxi := ConstructClass(P4, N4, Ch4[i]: Limit := 5^4);
     R := SetToSequence(Cxi) cat Ch4;
     if exists(pair){<x,y> : x, y in R | Order(&*<x,y>) gt 6} then
        break i;
     else
        Append(~classes4, Cxi);
     end if;
 end for;
 Order(&*pair);
 
 // Dimension 20
 time P5 := SplitExtension(GrpPerm, G, irr5[6]);
 assert Ngens(P5) eq 27;
 H5 := sub<P5 | [P5.i : i in [1..7]]>;
 assert GroupName(H5) eq "M11";
 N5 := sub<P5 | [P5.i : i in [8..27]]>;
 assert IsElementaryAbelian(N5);
 invs_H5 := [ x : x in Classes(H5) | x[1] eq 2];
 assert #invs_H5 eq 1;
 h5 := invs_H5[1][3];
 Ch5 := Class(H5, h5);
 Ch5 := SetToSequence(Ch5);
 assert #Ch5 eq 165;
 CPh5 := Centraliser(P5, h5);
 assert {FactoredOrder(Centraliser(N5, x)) : x in Ch5} eq {[<5, 8>]};
 assert #P5 div #CPh5 eq 165*5^12;
 classes5 := [];
 for i := 1 to 165 do
     Cxi := ConstructClass(P5, N5, Ch5[i]: Limit := 5^4);
     R := SetToSequence(Cxi) cat Ch5;
     if exists(pair){<x,y> : x, y in R | Order(&*<x,y>) gt 6} then
        break i;
     else
        Append(~classes5, Cxi);
     end if;
 end for;
 Order(&*pair);

 // Dimension 45
 time P6 := SplitExtension(GrpPerm, G, irr5[7]);
 assert Ngens(P6) eq 52;
 H6 := sub<P6 | [P6.i : i in [1..7]]>;
 assert GroupName(H6) eq "M11";
 N6 := sub<P6 | [P6.i : i in [8..52]]>;
 assert IsElementaryAbelian(N6);
 invs_H6 := [ x : x in Classes(H6) | x[1] eq 2];
 assert #invs_H6 eq 1;
 h6 := invs_H6[1][3];
 Ch6 := Class(H6, h6);
 assert #Ch6 eq 165;
 CPh6 := Centraliser(P6, h6);
 Ch6 := SetToSequence(Ch6);
 classes6 := [];
 assert {FactoredOrder(Centraliser(N6, x)) : x in Ch6} eq {[<5, 21>]};
 assert #P6 div #CPh6 eq 165*5^24;
 for i := 1 to 165 do
     Cxi := ConstructClass(P6, N6, Ch6[i]: Limit := 5^4);
     R := SetToSequence(Cxi) cat Ch6;
     if exists(pair){<x,y> : x, y in R | Order(&*<x,y>) gt 6} then
        break i;
     else
        Append(~classes6, Cxi);
     end if;
 end for;
 Order(&*pair);
 
 // Dimension 55
 time P7 := SplitExtension(GrpPerm, G, irr5[8]);
 assert Ngens(P7) eq 62;
 H7 := sub<P7 | [P7.i : i in [1..7]]>;
 assert GroupName(H7) eq "M11";
 N7 := sub<P7 | [P7.i : i in [8..62]]>;
 assert IsElementaryAbelian(N7);
 invs_H7 := [ x : x in Classes(H7) | x[1] eq 2];
 assert #invs_H7 eq 1;
 h7 := invs_H7[1][3];
 Ch7 := Class(H7, h7);
 Ch7 := SetToSequence(Ch7);
 classes7 := [];
 assert {FactoredOrder(Centraliser(N7, x)) : x in Ch7} eq {[<5, 27>]};
 CPh7 := Centraliser(P7, h7);
 assert #P7 div #CPh7 eq 165*5^28;
 classes7 := [];
 for i := 1 to 165 do
     Cxi := ConstructClass(P7, N7, Ch7[i]: Limit := 5^4);
     R := SetToSequence(Cxi) cat Ch7;
     if exists(pair){<x,y> : x, y in R | Order(&*<x,y>) gt 6} then
        break i;
     else
        Append(~classes7, Cxi);
     end if;
 end for;
 Order(&*pair);
