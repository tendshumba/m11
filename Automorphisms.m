/*
  Automorphisms of axial algebras in AlgGen form.

*/


/* 
  ============================================== Auxiliary functions. ==========================================

*/

  //  Declare a verbose setting for printing.
  declare verbose Automorphisms, 2;

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// This function computes the orbits of a Miyamoto group given as a matrix group on a list of axes.          +
//It takes as input the MiyamotoGroup and a list of axes.                                                    +                                                           +
//                                                                                                           +
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
MiyamotoOrbits := function(Grp, lst) 
  orbs := [];
  Aut := Grp;
  A := Parent(lst[1]);/*must be an algebra in AlgGen form.*/ 
  while #lst gt 0 do
    S := Vector(lst[1])^Aut;
    S := {@A!Eltseq(x):x in S@};
    Append(~orbs, S);
    lst := [x : x in lst | x notin S]; 
  end while; 
  return orbs;
end function;

/*====================================================================================================================
+function takes natural number arguments. If we have n vectors v_1, v_2,.., v_n, we want to find the n*(n+1)/2
+products using commutativity. I.e., we want v_iv_j with j>=i. We want to know the position of v_iv_j in the 
+list/sequence of products. v_1 has n products, v_2 will have n-1, v_3 n-3, etc, so an arithmetic progression with d=-1, 
+a=n.
======================================================================================================================*/	
Ind := function(n, i, j)
  if (n lt 1) or (i le 0) or (i le 0) then
     print " The arguments must be positive integers";
     return "fail";
  end if;
  if (i gt n) or (j gt n) then
     print "Error, both the second and third arguments must be less or equal to the first";
     return "fail";
  end if;
  if i gt j then
     print "the third argument must be greater or equal to the second";
     return "fail";
  end if;
  return IntegerRing()!((i-1)/2*(2*n-i+2))+j-i+1;//The position of v_iv_j is the sum of the products up to i-1 plus j
end function;

/*==========================================================================================================================
 * Multiply a sequence of algebra elements by a single vector.                                                             
 *
 * =======================================================================================================================*/

intrinsic BatchMultiply(L::SeqEnum[AlgGenElt], u::AlgGenElt) -> SeqEnum[AlgGenElt]
{  For a non-empty sequence L of algebra elements, find the products lu, with l in L  }
   require #L gt 0: "The sequence must be non-empty";
   require Parent(L[1]) eq Parent(u): "All arguments must belong to the same algebra.";
   return ApplyMatrixToVectors(AdMat(u), L);
end intrinsic;
// Version for Batch multiplying vectors in two lists. 
intrinsic BatchMultiply(L::SeqEnum[AlgGenElt], M::SeqEnum[AlgGenElt])->SeqEnum[AlgGenElt]
{  Given sequences L and M of algebra elements, find all producs uv with u in L and v in M. Since we assume commutativity,
   when L coincides with M, this will just be \#L\(\#L+1\)/2 products. }
   require #L gt 0 and #M gt 0: "The arguments must be non-empty";
   require Parent(L[1]) eq Parent(M[1]): "Both sequences must have elements of the same algebra.";
   l := #L;
   if L eq M then
      return &cat[BatchMultiply(L[[i..l]], L[i]) : i in [1..l]];
   end if;
   // L and M different (possibly having nonempty intersection)
   if #L ge #M then
      return &cat[BatchMultiply(L, M[j]) : j in [1..#M]];
   else
      return &cat[BatchMultiply(M, L[i]) : i in [1..l]];
   end if;
end intrinsic;

/*============================== Adjoint matrix ==================================================================*/

// First we need times, which exploits commutativity


intrinsic times(u::AlgGenElt, v::AlgGenElt)->AlgGenElt
{ 
   Given algebra elements u and v belonging to the same commutative algebra, form their product u*v.
}
   A := Parent(u);
   require Parent(v) eq A:" u and v must belong to the same algebra";
   if u eq A!0 or v eq A!0 then
      return A!0;
   end if;
   sup_u := Support(u);
   sup_v := Support(v);
   sup_int := sup_u meet sup_v;
   u_seq := Eltseq(u);
   v_seq := Eltseq(v);
   sup_uxsup_v := CartesianProduct(sup_u, sup_v);
   if sup_int ne {} then
      Square_int := CartesianPower(sup_int, 2);
      if exists{x : x in Square_int | x[1] ne x[2] } then// basically if |Square_int|> 1
         sum_square_int := &+[(u_seq[x[1]]*v_seq[x[2]]+u_seq[x[2]]*v_seq[x[1]])*(A.x[1])*(A.x[2]): x in Square_int | x[1] lt x[2] ];
      else
        sum_square_int := A!0;
	end if;
	sum_square_int+:= (&+[u_seq[i]*v_seq[i]*(A.i)*(A.i) : i in sup_int]);
    else
	sum_square_int := A!0;
    end if;
    if ((sup_int ne {}) and (sup_uxsup_v ne Square_int)) then
	// Find the complement and sum over this
      comp := [x : x in sup_uxsup_v | x notin Square_int ];
      comp_sum := &+[ u_seq[x[1]]*v_seq[x[2]]*(A.x[1])*(A.x[2]) : x in comp];
    else
      comp_sum := A!0;
    end if;
    if sup_int eq {} then 
      comp_sum := &+[ u_seq[x[1]]*v_seq[x[2]]*(A.x[1])*(A.x[2]) : x in sup_uxsup_v ];
    end if;
    return sum_square_int +comp_sum;
end intrinsic;

intrinsic AdMat(a::AlgGenElt) -> AlgMatElt
{
   Given a general algebra element a, find the matrix of the adjoint endomorphism x:->ax, relative to the 
	standard basis. 
}
   A := Parent(a);
   return Matrix([times(a, A.i) : i in [1..Dimension(A)]]);// relative to the standard basis coordinates are obvious
end intrinsic;

/*===========================================================================================================================
 * Utitilities for applying a matrix to a number of vectors all at once. 
 *
 *==========================================================================================================================*/
intrinsic ApplyMatrixToVectors(M::AlgMatElt, L::SeqEnum[ModTupFldElt]) -> SeqEnum[ModTupFld]
{ Given an n by m matrix M, and a non-empty sequence L of vectors of degree n, where M and the vectors in L
are over the same field, return the sequence \[v*M:v in L\] of degree m vectors }
  require #L ge 1: "The sequence must be non-empty";
  require Degree(L[1]) eq Nrows(M): "The degree of vectors is not compatible with the matrix.";
  require BaseRing(M) eq BaseRing(Parent(L[1])): "The vectors and the matrix must be over the same field.";
  MM := Matrix(L)*M;
  return [MM[i] : i in [1..#L]];
/* Magma vectors are row vectors so multiplication on the right by M of the matrix whose rows
are the vectors of L gets all the images at once.*/
end intrinsic;
/*=====================================================================================================
Version for algebra elements
Could be modified so it can take non-square matrices and have a second algebra as option for the output.
=====================================================================================================*/
intrinsic ApplyMatrixToVectors(M::AlgMatElt, L::SeqEnum[AlgGenElt]) -> SeqEnum[AlgGenElt]
{ Given an nxn matrix M, and a non-empty sequence Lof algebra elements over the same field as M, return
	the sequence \[v*M|v in L\] as algebra elements}

  require #L gt 0: "The sequence must be non-empty.";
  require Nrows(M) eq Ncols(M) : "M must be square.";
  LL := [Vector(L[i]) : i in [1..#L]];
  A := Parent(L[1]);
  L_out := ApplyMatrixToVectors(M, LL); 
  return [A!L_out[i] : i in [1..#L]] ;
end intrinsic;

/*========================================================================================================================
 * Projection to a subspace.
 *
 *=======================================================================================================================*/

intrinsic FindPerpWithRespectToForm(A::AlgGen, V::ModTupFld, M::ModTupFld : bool:= true, form := IdentityMatrix(BaseField(A),Dimension(A)))->ModTupFld
{
   Given an algebra A, a subalgebra V of A, given as a linear space, and a subspace M of V, find all the elements of V which
   are perpendicular to all the elements of M. Optional parameters are form: the Frobenius form, and a boolen which is set to
   true by default indicating that A has a form. Set to false otherwise.
} 
   basV := Basis(V);
   basM := Basis(M);
   if IsIdentity(form) then 
      bool, U := HasFrobeniusForm(A);
      if bool eq false then 
         return "fail";
      end if;
   else
      require Type(form) eq AlgMatElt: "The form must be a matrix";
      require (Nrows(form) eq Ncols(form)) and (Nrows(form) eq Dimension(A)): "The form must be a sqaure matrix if the same size as the dimension of A.";
  end if;
  m := #basV;
  k := #basM;
  F := BaseField(A);
  B := ZeroMatrix(F, k, m);
  for j :=1 to k do
     for i := 1 to m do
        B[j][i]+:= FrobeniusFormAtElements(A!basV[i], A!basM[j], form); 
     end for;
  end for;
  sol := NullspaceOfTranspose(B);
  if Dimension(sol) ne 0 then 
     bas := [&+[V.j*(sol.i)[j] : j in [1..Dimension(V)]] : i in [1..Dimension(sol)] ]; //sol.i@BasisMatrix(V) works too
     return sub<VectorSpace(A)|bas>;
  else 
     return sol;
  end if; 
end intrinsic;

intrinsic ProjectionToSubspace( A::AlgGen, V::ModTupFld, form::AlgMatElt) -> AlgMatElt
{
  Given an algebra A admitting a form "form", and a subspace V of A as a linear space, return the projection map P\: A \--\> A 
  such that vP\=v for v in V and 0 on elements of the complement of V in A.
}
  require V subset VectorSpace(A): "The given space is not a linear subspace of A";
  require Ncols(form) eq Nrows(form): "The form must be a square matrix.";
  require Nrows(form) eq Dimension(A): "The form must be compattible with the algebra";	
  bas := Basis(V) cat Basis(FindPerpWithRespectToForm(A, VectorSpace(A), V: form:=form)); 
  bas_change := Matrix(bas);
  m := Dimension(V);
  P_bas := DiagonalJoin(IdentityMatrix(F, m), ZeroMatrix(F, Dimension(A)-m)) where F is BaseRing(A); 
  return bas_change^(-1)*P_bas*bas_change;
end intrinsic;

/*======================================================================================================================
 * Find the annihilator of a subspace of an algebra acting on another subspace
 *
 * ===================================================================================================================*/

intrinsic AnnihilatorOfSpaceUnderActionOfSubspace(A:: AlgGen, U:: ModTupFld, W:: ModTupFld) -> ModTupFld
{
  Given an algebra A, subspaces U and W given as linear space, find the annihilator of the adjoint action of U on W.
}
  require U subset VectorSpace(A) and W subset VectorSpace(A) : "U and W must be subpsaces of A.";
  m := Dimension(U);
  m_1 := Dimension(W);
  acts := true;
  prods := [];
  bas_U := Basis(U);
  bas_W := Basis(W);
  t0 := Cputime();
  L1 := [A!bas_U[i] : i in [1..m]];
  L2 := [A!bas_W[i] : i in [1..m_1]]; 
  for j := 1 to m_1 do /* fix j. */
    prods_j := BatchMultiply(L1, L2[j]);
    if exists{v : v in prods_j | v notin W} then
      print "error, the second argument must act on the third";
      acts := false;
      break j;
    else
      prods cat:= prods_j;
    end if;
  end for;
  vprintf Automorphisms, 1: "products in the action of U on W found in %o seconds \n", Cputime(t0);
  require acts eq true : "U must act on W";
  sols := Solution(BasisMatrix(W), [Vector(v) : v in prods]);
  Nspace := Nullspace(HorizontalJoin([Matrix(sols[[(i-1)*m+1..i*m]]) : i in [1..m_1]]));
  if m eq Dimension(A) then
    return Nspace;
  else
    vecs := [&+[(Nspace.j)[i]*bas_U[i] : i in [1..m]] : j in [1..Dimension(Nspace)]];
		return sub< U | vecs >;
  end if;
end intrinsic;

/*=============================================== Subalgebra utilities =================================================== */

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Find the structure constants in a subalgebra U of an algebra A.                                                      +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic FindStructureConstantsSubalgebra(A::AlgGen, U::ModTupFld:subalgebra_check := false) -> SeqEnum[ModTupFld]
{	
   Given An axial algebra A and a subalgebra U, find the structure constants c_\{i,j\}^k, where 
   u_i*u_j=Sum_\{i=1\}^m c_\{i,j\}^ku_k, with u_1, u_2,...,u_m a basis for U. Here m:=dim(U). 
   The function returns a sequence of m-long vectors with structure constants corresposing to 
   product u_i*u_j for j ge i. We will not check that U is a subalgebra by default, but changing subalgebra_check to true will cause a check.
}
   m := Dimension(U);
   if subalgebra_check eq true then
      require IsSubalgebra(A, U): "U must be a subalgebra";/*this check takes half the time when used.
      Use a key. In any case, it will fail if not a subalgebra.*/
   end if;
   bas := Basis(U);
   bas_alg := [A!bas[i] : i in [1..m]];
   //I want products of bases elements written as linear space elements.
   t := Cputime(); 	
   vec_prods := BatchMultiply(bas_alg, bas_alg);// we will get the m*(m+1)/2 products
   if exists{ v : v in vec_prods | v notin U} then
      error "The second argument is not a subalgebra of the first";
   end if;
   prods := [Vector(vec_prods[i]) : i in [1..#vec_prods]];
   vprintf Automorphisms, 1: " products of basis vectors found in %o seconds.\n", Cputime(t);
   t1 := Cputime();
   tens := Solution(BasisMatrix(U), prods);
   vprintf Automorphisms, 1: "Coordinates of vectors found in %o seconds.\n", Cputime(t1);
   return tens;	
end intrinsic;

//================== Find all structure constants given a sequnce that gives a_ia_j with $j\geq i$. =======================

intrinsic AllStructureConstants(L::SeqEnum[ModTupFldElt]) -> SeqEnum[FldElt]
{
   Given a sequence L of vectors (a_\{ij\}^k), i,k ranging between 1 and n, and j greater or equal to i, form the sequence of 
   length n^3 with entries a_\{ij\}^k. L above may be obtained using GetStructureConstants. We exploit the fact that axial 
   algebras are commutative, by definition.
 }
   length := #L;
   sols := Roots(Polynomial(IntegerRing(),[-2*length,1,1]));
   /*From the preamble if an algebra A has dimension n, then L will have length 1/2*(n(n+1)) so 2*length=n(n+1)
   or equivalently, 0=n^2+n-2*length, so n must satisfy the equation 0=x^2+x-2*length.*/
   pos_sol := [x[1] : x in sols|Sign(x[1]) eq 1];/*positive root of the equation.*/
   require #pos_sol ne 0: "The length of L must be a positive integer";
   n := pos_sol[1];
   require Degree(L[1]) eq n: "The degree of vectors must be n";
   all_vecs := [];
   for i := 1 to n do 
      for j := 1 to n do
         vec :=  L[ind] where ind is (( i le j) select Ind(n, i, j) else Ind(n, j, i));
         Append(~all_vecs, vec);
      end for;
   end for;
   return &cat[Eltseq(all_vecs[i]) : i in [1..n^2]];
end intrinsic;

/*=============================================================================================================================
 * For an algebra A and a subspace U of A as a linear space, check if U is a subalgebra
 *
 * ==========================================================================================================================*/
      /* I could use the following one liner but it doesn't allow for showing failures.

	return forall{i : i in [1..m] | forall{v : v in prods where prods := BatchMultiply([A!U.j : j in [i..m]], A!U.i) | v in U}};
*/
intrinsic IsSubalgebra(A:: AlgGen, U::ModTupFld) -> BoolElt
{ For an algebra A and a linear space U, determine if U is a subalgebra}
  require U subset VectorSpace(A): "The second argument must be a linear subspace of the first.";
  m := Dimension(U);
  require m gt 0: "The second argument must be non-zero.";
  bool := true;
  count :=1;
  while count le m do
    for i:= 1 to m do
      t := Cputime();
      u := A!U.i;
      L := [A!U.j : j in [i..m]];
      prods := BatchMultiply(L, u);
      if exists(v){v : v in prods | v notin U} then
         bool := false;
         count := m+1;
	 vprintf Automorphisms, 2: "Check for i taking the value %o performed in %o seconds and (U.%o)*(U.%o) is not in U \n", i,
         Cputime(t), i, Index(prods,v)-1+i;
         break i;
      else
        count +:=1;
      end if;
      vprintf Automorphisms, 2: "Check for i taking the value %o performed in %o seconds \n", i, Cputime(t);// use vprintf here
    end for;
  end while;
  return bool;
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Suppose that A is an axial algebra and let H be a subalgebra of the Miyamoto group.  +
+ Find a subalgebra of A with Miyamoto group H.                                        +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic SubalgebraCorrespondingToSubgroup(A::AlgGen, H::GrpMat:axes := false, Miyamoto_group := false) -> ModTupFld
{
   Let A be an axial algebra and let H be a subgroup of the Miyamoto group G:=Miy(A).
   Find the subalgebra whose Miyamoto group is H. Optional parameters are a sequence
   of axes and a Matrix group Miy.
}
   n := Dimension(A);
   require Nrows((H.1)) eq n: "H must be a matrix group of degree equal to dim(A).";
   if Type(axes) eq BoolElt then
      axes := [A.i : i in [1..n] | IsIdempotent(A.i) ];
   else
      require Type(axes) eq SeqEnum and Type(axes[1]) eq AlgGenElt and forall{x : x in axes | IsIdempotent(x)}:
      "the optional input axes must be a sequence of idempotents.";
      require Dimension(Subalgebra(IndexedSet(axes))) eq n:" The sequence axes must generate the algebra.";//change to Subalgebra
   end if;
   if Type(Miyamoto_group) eq BoolElt then
      _,Miyamoto_group,_,_ := MiyamotoGroup(axes);
   else
      require Type(Miyamoto_group) eq GrpMat and Degree(Miyamoto_group) eq n:
      "The option Miyamoto_group must be a matrix group compatible with the given algebra.";
   end if;
   require H subset Miyamoto_group: "The given group H must be a subgroup of the Miyamoto group.";
   orbs:=MiyamotoOrbits(H, axes);
   corresponding_axes := {@@};
   for i := 1 to #orbs do
      orb := orbs[i];
      rep := orb[1];
      bool := (TauMapMonster(rep) in H);
      if bool eq true then
         corresponding_axes join:= orb;
      end if;
   end for;
   return Subalgebra(corresponding_axes);
end intrinsic;
/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ A function to find the subalgebra generated by a sequence of algebra vectors.                                  +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic Subalgebra(L::SetIndx[AlgGenElt] )-> ModTupFld 
{
   Given an indexed set L of axial vectors, return the subalgebra of the parent algebra that is generated by L. 
} 
   require #L gt 0: "L must be nonempty";
   A := Parent(L[1]); 
   n := Dimension(A);
   W := VectorSpace(A);
   lst := [Vector(L[i]) : i in [1..#L]];/*set up the vectors in L as ordinary vectors*/
   if #L eq 1 and W!0 in lst then
      return sub<W | W!0>;
   end if;
   /* we start by finding a maximally independent set.*/
   V := sub< W | lst >;	
   max_independent_set := [A!bas[i] : i in [1..Dimension(V)]] where bas is Basis(V);
   bool, VV := ExtendMapToAlgebraAutomorphism(max_independent_set, max_independent_set: check_automorphism := false);
   if bool eq true then 
      return W;
   else
      return VV;
   end if; 
end intrinsic;

/*================================================== Group, automorphism utilities=======================================*/

//=========================== Check that a map is an automorphism =======================================================
intrinsic IsAutomorphism(A:: AlgGen, M::AlgMatElt: generators := []) -> BoolElt
{  Check if a given matrix represents an automorphism of an algebra relative to the standard basis }
   F := BaseRing(A);
   require BaseRing(M) eq F: "Both arguments must be over the same field.";
   require IsInvertible(M) : "The second argument must be invertible.";
   bas_A := Basis(A);
   if #generators gt 0 then
      require Type(generators) eq SeqEnum: "the generators must be in a sequence.";
      require Type(generators[1]) eq AlgGenElt: "Generators must be algebra elements";
      require Parent(generators[1]) eq A: "The generators must belong to the first argument";
      L := generators;
      vprintf Automorphisms, 1 : " There are user defined generators\n";
   else 
      L := bas_A;
   end if;
   bas_prods := BasisProducts(A); // essentially structure constants
   /* We could write much shorter code but it will do unnecessary work in the case
	that some pair of vectors fail the homomorphic requirement*/

   if L ne bas_A then // We start with the case where a user supplied generators different from the standard basis.
      if exists{ v : v in L | v notin bas_A } then// the case where some generators are not in the std basis.
         nice := [ v : v in L | v in bas_A ];// if this is empty, then all the gens are not in bas_A
         vprintf Automorphisms, 1: "There are %o nice generators\n", #nice;
         bad := [v : v in L | v notin nice ]; 
 	 ims_bad := ApplyMatrixToVectors(M, bad);
 	 if #nice ne 0 then // there are some  standard basis vectors in the generators
	    ims_nice := ApplyMatrixToVectors(M, nice);
	    // It pays to find the products stage by stage especially when the test fails.
	    for i := 1 to #nice do
	       ims_prods := BatchMultiply(ims_nice[[i..#nice]], ims_nice[i]);// products of images, {(u*M)*(v*M): u,v in  nice}
               prods := [ bas_prods[Index(bas_A, nice[i])][Index(bas_A, nice[j])] : j in [i..#nice]];
	       prods_ims := ApplyMatrixToVectors(M, prods);// {(uv)*M:u,v in nice}
	       if exists(j){j : j in [1..#prods] | ims_prods[j] ne prods_ims[j] } then
	          vprintf Automorphisms, 1: " ((A.%o)*M)*((A.%o)*M) not equal to ((A.%o)*(A.%o))*M\n", i, j+i-1, i, j+i-1;
	          return false;
	       end if;
	       // multiply the nice vectors with some "bad" ones.
	       prods := BatchMultiply(bad, nice[i]);
	       prods_ims := ApplyMatrixToVectors(M, prods);
	       ims_prods := BatchMultiply(ims_bad, ims_nice[i]);
               if exists{j : j in [1..#prods] | prods_ims[j] ne ims_prods[j] } then
	          return false;
	       end if;
	    end for;
         end if;
         // multiply the "bad" vectors amongst themselves
         m := #bad;
         for i := 1 to m do
            prods := BatchMultiply(bad[[i..m]], bad[i]);
	    prods_ims := ApplyMatrixToVectors(M, prods);
	    ims_prods := BatchMultiply(ims_bad[[i..m]], ims_bad[i]);
	    if exists{ j : j in [1..#prods] | prods_ims[j] ne ims_prods[j]} then
	       return false;
	    end if;
         end for;// if we get here the test was passed for the case with some non-standard gens	
         return true;	
      end if;
   end if;
   // At this stage the sequnce L is all of bas_A or is entirely contained there
   t0:= Cputime();
   ims_L := ApplyMatrixToVectors(M, L);
   vprintf Automorphisms, 1: " images of vectors in L found in %o seconds\n", Cputime(t0);
   m := #L;
   vprintf Automorphisms, 1: "We check on the %o generators\n", m;
   for i := 1 to m do
      t0 := Cputime();
      prods := [bas_prods[Index(bas_A, L[i])][Index(bas_A, L[j])] : j in [i..m]];
      vprintf Automorphisms, 1: "for i eq %o, products of the generators found in %o seconds\n",i, Cputime(t0);
      t1 := Cputime();
      prods_ims := ApplyMatrixToVectors(M, prods);
      vprintf Automorphisms, 1: "images of products found in %o seconds\n", Cputime(t1);
      t2 := Cputime();
      ims_prods := BatchMultiply(ims_L[[i..m]], ims_L[i]);/* Since automorphisms permute generators, check
      if the ims are actually some of the basis vectors, then we don't need to actually perform the mutlitiplication.*/
      vprintf Automorphisms, 1: "for i eq %o products of images formed in %o seconds\n", i, Cputime(t2);
      if exists(j){j : j in [1..#prods] | prods_ims[j] ne ims_prods[j]} then
         vprintf Automorphisms, 1: " The pair %o,%o fails the homomorphism test\n", i, j+i-1;
         return false;
      end if;
   end for;
   // if we get here then the test was passed
   return true;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given a list of axes for an algebra, give the corresponding permutation +
+ or matrix group. For the permutation case, the parameter full will be   +
+ set to false, otherwise a permutation group of degree equal to the size +
+ of the axes will be produced.                                           +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic MiyamotoGroup(L::SeqEnum[AlgGenElt]: axes_check := false) -> GrpPerm, GrpMat, Map, MonStgElt, SetIndx 
  {
   Given a sequence L of axes in an algebra, return the corresponding group.
  }
   require #L eq #SequenceToSet(L): "L must consist of distinct algebra elements.";
   t0 := Cputime();
   require forall{x : x in L | IsIdempotent(x)}: "All the elements of L must be idempotent";
   vprintf Automorphisms, 1:  "idempotency check completed in %o\n", Cputime(t0);
   if axes_check then
      require forall{x : x in L | HasMonsterFusionLaw(x)} : "L must consist of axes";
   end if;
   A := Parent(L[1]);
   basis := Basis(A);
   axes := [];
   taus := [];
   sigmas := [];
   jordans := [];
   twins := [];// this part is actually important for later
   for i := 1 to #L do// remove twins and Jordan axes
         tau := TauMapMonster(L[i]);
         if ((not IsIdentity(tau)) and (not tau in taus)) then
	    Append(~taus, tau);
	    Append(~axes, L[i]);
	 end if; 
    end for;
    /*we will reduce the number of generators of the matrix group.*/
    F := BaseField(A);
    n := Nrows(taus[1]);
    t0 := Cputime();
    prods := [ taus[1]*taus[i] : i in [2..#taus]];
    vprintf Automorphisms, 1: "products of tau maps of axes with that of the first axis found in %o seconds\n", Cputime(t0);
    t0 :=Cputime();
    orders := [Order(t) : t in prods ];
    vprintf Automorphisms, 1: "Orders of products found in %o seconds\n", Cputime(t0); 
    t0 := Cputime();
    m, ind := Maximum(orders);
    //I_n := IdentityMatrix( F, n);
    maxes := [i : i in [1..#orders] | orders[i] eq m];
    vprintf Automorphisms, 1: "The number of tau maps of maximum order %o "*
    "is %o found in %o seconds\n", m, #maxes, Cputime(t0);
		
     t0 := Cputime();
     lst := taus[[1]];
     used_prods := [prods[ind]];
     max_prods := [ prods[i] : i in maxes];
     for i -> y in max_prods[[2..#max_prods]]  do // can start from 1
        if #used_prods lt 3 then
           if not y in used_prods then
	      if forall{ t : t in used_prods | not IsIdentity(y*t)} then 
	         Append(~used_prods, y);
	      end if;
	   end if;
	   elif #used_prods ge 3 then
	   last_ind := i;
	   break ;
	end if;
     end for;
     vprintf Automorphisms, 1: "The number of used products is %o\n", #used_prods;
     Gp := MatrixGroup< n, F | used_prods >;// we could find as many independent posible D_{2m}s and randomly choose 3
     vprintf Automorphisms, 1: "The initial group formed in %o seconds\n", Cputime(t0);
     t := Cputime();
     vprintf Automorphisms, 1: "Reducing the number of generators of the Miyamoto group..\n";
	
     /*seems easy to form groups, and tests seem to suggest membership
      testing is not that expensive when the group has few generators*/	
      t0 := Cputime();
      if #used_prods gt 2 then
         tups := [<i, j> : i, j in [1..3] | i lt j];
         for x in tups do
            G := sub< Gp | used_prods[[x[i] : i in [1, 2]]] >;
	    if G eq Gp then
	       Gp := G;
	       vprintf Automorphisms, 1: "The numbers of generators of the current group reduced to two\n";
	       break x;
	    end if;
	 end for;
      end if;
      for tau in taus do
         if not tau in Gp then
	    Gp := MatrixGroup< n, F | tau, Gp >;
	    vprintf Automorphisms, 1: "A generator added\n";
	 end if;
      end for;
      vprintf Automorphisms, 1: "The number of generators of the Miyamoto group reduced in %o seconds\n",     Cputime(t0);
      Miy := Gp; 
      vprintf Automorphisms, 1: "The Miyamoto group is %o\n", GroupName(Miy);
      t0 := Cputime();
      gens := [ x : x in Generators(Miy)];
      vprintf Automorphisms, 1: "The number of generators of Miy is %o\n", #gens;
	/* When generating axes are not closed or an orbit consists of twin pairs, then we will
	  need to produce the closure and then find generators which are not involutions since
	  there isn't a one-to-one correspondence between axes and tau involutions.*/
      closure := &join MiyamotoOrbits(Gp, axes);
      vprintf Automorphisms, 1:"closure of the axet found in %o seconds.\n", Cputime(t0);
      if #closure gt #axes then// here there are twins in an orbit
         orbs := MiyamotoOrbits(Gp, closure);
         all_axes := closure;
	 invs_gens := [g : g in gens| Order(g) eq 2];
	 if not IsEmpty(invs_gens) then
	    classes := Classes(Miy);
	    for i -> x in invs_gens do
	    /*Find a generator which is not an involution to replace x. */
	       G := sub< Miy | [g : g in gens | g ne x]>;
	       for cc in classes do
	          if cc[1] gt 2 then
		     orb := cc[3]^Miy;
		     for y in orb do
		       	if not y in G then
			   if sub< Gp | G, y> eq Miy then
			      gens[i] := y;
			   end if;
			end if;
		     end for;
		  end if;
               end for;
	    end for;	
	    Gp := sub< Gp | gens >;
            Miy := Gp;
	 end if;
      else
         orbs := MiyamotoOrbits(Gp, axes);
	 all_axes := IndexedSet(SequenceToSet(axes));
      end if;
      // after this we must form the permutation representation of the Miyamoto group
      t0 := Cputime();
      //perms := [[Position(all_axes, all_axes[i]*x) : i in [1..#all_axes]] : x in gens];
      perms := [ApplyMatrixToVectors(Matrix(x), IndexedSetToSequence(all_axes)) : x in gens];
      perms := [[Position(all_axes, x[i]) : i in [1..#all_axes]] : x in perms];
      Miy_perm := PermutationGroup<#all_axes|perms>;
      vprintf Automorphisms, 1: "The permutation representation of the Miyamoto group found in %o seconds.\n", Cputime(t0);
      t0 := Cputime();
      f := hom<Miy_perm -> Miy | [<Miy_perm.i, gens[i]> : i in [1..#gens]]>;
      vprintf Automorphisms, 1: "The isomorphism between the permutation and matrix representation found in %o seconds.\n", Cputime(t0);
      return Miy_perm, Miy, f, GroupName(Miy_perm), all_axes;
end intrinsic;

declare verbose GroupFromAxes, 1;
intrinsic GroupFromAxes(L::SeqEnum[AlgGenElt]: axes_check := false) -> GrpPerm, GrpMat, Map, MonStgElt, GrpMat
{  Produce the biggest possible obvious group of automorphisms of the algebra generated by the input list. }
   require not IsEmpty(L): "The argument must be a non-empty sequence.";
   A := Parent(L[1]);
   require Subalgebra(IndexedSet(L)) eq VectorSpace(A) : "The input must be a generating set of the parent algebra.";
   if axes_check then
      require forall{ x : x in L | HasMonsterFusionLaw(x)}: "The arguments must consist of axes.";
      /* perhaps having the matrix form of the Miyamoto group as an option and using that to test
      orbit representatives is the best idea here.*/
   end if; 
   F := BaseRing(A);
   // First remove twins (hence duplicate tau maps) and jordan axes( sigma maps).
   taus := [TauMapMonster(x) : x in L];
   taus_distinct := [];
   axes := [];
   jordans := [];
   sigmas := [];
   for i := 1 to #L do
      if IsIdentity(taus[i]) then
         sigma := SigmaMapMonster(L[i]);
	 Append(~jordans, L[i]);
	 Append(~sigmas, sigma);
      else
         if not taus[i] in taus_distinct then
	    Append(~taus_distinct, taus[i]);
	    Append(~axes, L[i]);
	 end if;
      end if;
   end for;
   vprintf Automorphisms, 1: "The number of sigma maps is %o.\n", #sigmas;
   Miy_p, Miy, isom, gpname, all_ax := MiyamotoGroup(axes); 
   aut := AutomorphismGroup(Miy_p);
   out := [ x : x in Generators(aut) | not IsInnerAutomorphism(x) ]; 
   gens_miy_p := SetToSequence(Generators(Miy_p));
   gens_miy := [x@isom : x in gens_miy_p];
   if IsEmpty(out) then
      if IsEmpty(sigmas) then
         return Miy_p, Miy, isom, gpname, Miy;
      end if;
      gens := gens_miy cat sigmas;
      gens_p := gens_miy_p cat [Sym(#all_ax)![Position(all_ax, all_ax[i]*sigmas[j]) : i in [1..#all_ax]] : j in [1..#sigmas]];
      perm_gp := PermutationGroup<#all_ax | gens_p>;
      mat_gp := MatrixGroup<Dimension(A), F | gens>;
      return perm_gp , mat_gp, hom<perm_gp -> mat_gp| [<perm_gp.i, mat_gp.i> : i in [1..#gens_p]]>, GroupName(perm_gp), Miy; 
   end if;
   out_extension := true;
   perms := [(x in axes) select taus[Index(axes, x)]@@isom else TauMapMonster(x)@@isom : x in all_ax];
   nice_gens := [ ];
   out_perms := [];
   nice := [];
   for phi in out do
      phi_p := Sym(#all_ax)![Position(perms, perms[i]@phi) : i in [1..#all_ax]];
      Append(~out_perms, phi_p);
   end for;
   for j -> phi in out do
      try 
         all_ax_seq := IndexedSetToSequence(all_ax);
	 bool, ext := ExtendMapToAlgebraAutomorphism(all_ax_seq, [all_ax_seq[i^out_perms[j]] : i in [1..#all_ax]]);
	 if bool then
	    Append(~nice_gens, phi);
	    Append(~nice, ext);
	 end if;
      catch e
         out_extension := false;
	 break j;
      end try;
   end for;
   if #nice lt #out then
      out_perm := PermutationGroup<#all_ax | out_perms >;
      extensions := nice;
      for x in {y : y in out_perm | (not IsIdentity(y)) } do 
         try 
	    bool, ext := ExtendMapToAlgebraAutomorphism(all_ax_seq, [all_ax_seq[i^x] : i in [1..#all_ax]]);
	    if bool then
	      if not ext in nice then
	         Append(~extensions, ext);
	      end if;
	    end if;
	 catch e
	 vprintf GroupFromAxes, 1: "There was an error.\n";
	 end try;
      end for; 
   else
      extensions := nice;
   end if;
   // where one of the generators of out doesn't extend we will need to reduce the number of generators.
   // we skip that for now (the group order greater than 4)
   G_mat := MatrixGroup<Dimension(A), F | [x : x in Generators(Miy)] cat extensions cat sigmas >;
   gens_Gp := [[Position(all_ax, all_ax[i]*x) : i in [1..#all_ax]] : x in Generators(G_mat)];
   G_perm := PermutationGroup<#all_ax | gens_Gp>;
   return G_perm, G_mat, hom<G_perm -> G_mat | [ <G_perm.i, G_mat.i> : i in [1..Ngens(G_perm)]]>, GroupName(G_perm), Miy; 
end intrinsic;

//=================================================Check that an involutive matrix is induced by an axis or axes.====================================

intrinsic IsInducedFromAxis(A::AlgGen, M::AlgMatElt: form := false, fusion_values := <1/4,1/32>, automorphism_check := true, length := 1) -> BoolElt,AlgGenElt
{
  Given a square matrix which is involutive, and compatible with A, determine if it is induced by an axis a. The default fusion values 
  are M(1/4,1/32), but can be changed to any arbitrary values. The switch to check if M is automorphic is turned on by default, but can be switched off.
  The function returns a boolean value true if true, as well as any such axi(e)s that induce M. If false, only false will be returned. If the algebra is
  Frobenius we assume that axes are of length 1, but this parameter can be changed.
}
  n := Dimension(A);
  require Nrows(M) eq Ncols(M) and Ncols(M) eq n: "The matrix M must be a sqaure matrix of size equal to dimension of the algebra.";
  F := BaseField(A);
  I_n := IdentityMatrix(F, n);
  require M ne Parent(I_n)!0: "The given matric must be non-zero";
  require M^2 eq I_n and M ne I_n: "The given matrix is not involutive.";
  require BaseRing(M) eq F or forall{i : i in [1..n] | forall{j : j in [1..n] | IsCoercible(F,M[i][j])}}: "The entries of M must be over the same field as A, 
  or should be coercible into the base field of A.";
  if automorphism_check eq true then
    require IsAutomorphism(A, M): "The given matrix is not an automorphism";
  end if;
  if fusion_values ne <1/4,1/32> then
    require fusion_values[1] in F and fusion_values notin {<1,0>,<0,1>}: "The fusion values must be in the base field and distinct from 0 and 1.";
  end if;
  alpha := fusion_values[1];
  beta := fusion_values[2];

  W := Eigenspace(M, -1);// The negative space
  U := AnnihilatorOfSpace(A, W);
  bool, one := HasOne(A);
  if bool then
    // we use the fact that if a exists such that $\tau_a=M$, then a=beta*one+x
    // x in Ann([A,M]). First we try ordinary axes.
     if Dimension(U) eq 0 then
        return false, {@ @};
     // we can prove that if U=0 then M cannot be induced by an axis.
     // Key obsrvation is that a-alpha*one, a-beta*one are nonzero, and assuming
     // a is type Jordan alpha or M(alpha, beta), they are nonzero annihilators respectively. 
     end if; 
    ordinary := FindAllIdempotentsInCoset(beta*one, U:form := form, length := 1);
    jordans := FindAllIdempotentsInCoset(alpha*one, U:form := form, length := 1) join
    FindAllIdempotentsInCoset(alpha*one, U:form := form, length := 2);
    return not IsEmpty(X), X where X := {@x : x in ordinary join jordans | HasMonsterFusionLaw(x) @};
  else
    // find a in $A_M={u\in A|u*M eq u}$.
    V := Eigenspace(M, 1); 
    //positiveW := Eigenspace(t_a,1);// the positive space of the map
    m1 := Dimension(V);
    R := PolynomialRing(F,m1);
    //V := Eigenspace(t_a, -1);// the negative space
    m2 := Dimension(W);// roles of V and W reversed here
    bas_W := Basis(W);
    bas_V := Basis(V);
    t0 := Cputime();
    prodsV := BatchMultiply(L, L) where L := [A!bas_V[i] : i in [1..m1]];
    vprintf Automorphisms, 1: "The products of basis vectors of the positive part of the map found in %o seconds.\n", Cputime(t0);
    t0 := Cputime(); 
    ads_W := [AdMat(A!w) : w in bas_W];
    vprintf Automorphisms, 1: "The odjoint matrices of basis vectors of the negative part of the map found in %o seconds.\n", Cputime(t0);
    AA := BasisMatrix(V); //(\alpha_{ij})

    /* we need to speed up the formation of linears. It reduces from 28725.610 to 7.3 seconds plus 2.830
    for A_286 for M_11, where dimW is 132 and the positive part is 154-dimenional.*/
    t0 := Cputime(); 
    ads_on_Vs := [ApplyMatrixToVectors(ads_W[i], bas_V) : i in [1..m2]]; // apply the adjoints to the basis of V in batches
    vprintf Automorphisms, 1: "The adjoint matrices of the basis elements of W applied to the basis vectors of V in %o seconds.\n", Cputime(t0); 
    t0 := Cputime(); 
    linears := &cat[[&+[(ads_on_Vs[i][j])[l]*R.j : j in [1..m1]]-beta*bas_W[i][l] : l in [1..n]] : i in [1..m2]];
    vprintf Automorphisms, 1: "Linear relations emanating from the action on the minus part found in %o seconds.\n", Cputime(t0);
    ordinary := FindAllIdempotents(A, V: form := form, length := length, extra_rels := linears);
    ordinary := (not IsEmpty(ordinary)) select {@ x : x in ordinary | HasMonsterFusionLaw(x) @} else ordinary;
    //now check also that the map is not induced by Jordan axes too. If induced by
    // ordinary axes, for any a, if a jordab axis exists corresponding to t_a, then
    // j is in (alpha/beta)*a+annW
    if not IsEmpty(ordinary) then
      jordans := &join[FindAllIdempotentsInCoset((alpha/beta)*a, U) : a in ordinary];
      jordans := (not IsEmpty(jordans)) select {@ x : x in jordans | HasJordanFusionLaw(x) @} else jordans; 
    else
      t0 := Cputime();
      linears := &cat[[&+[(ads_on_Vs[i][j])[l]*R.j : j in [1..m1]]-alpha*bas_W[i][l] : l in [1..n]] : i in [1..m2]];
      vprintf Automorphisms, 1: "Linear relations emanating from the action on the minus part found in %o seconds.\n", Cputime(t0);
      jordans := FindAllIdempotents(A, V: form := form, length := length, extra_rels := linears);
      //jordans := (not IsEmpty(jordans)) select {@ x : x in jordans | HasMonsterFusionLaw(x) @} else jordans;
      jordans := (not IsEmpty(jordans)) select {@ x : x in jordans | HasJordanFusionLaw(x) @} else jordans;
    end if;
    return not IsEmpty(X), X where X := ordinary join jordans;
  end if;
end intrinsic;

//=======================Find the tau map for an axis wrt to some $C_2$-grading======================

intrinsic TauMap(a::AlgGenElt, T::Tup)-> AlgMatElt
{
   Suppose a is an algebra element and T is a tuple made up of two sequences consistsing of eigenvalues in a 
   plus part and a minus part of a C_2 grading. Produce the corresponding tau involution.
}
   A := Parent(a);
   require a ne 0: "a must be nonzero.";
   require #T[1] gt 0 and #T[2] gt 0: "Both parts of T can't be empty.";
   ad_a := AdMat(a);
   eigs := Eigenvalues(ad_a);
   e_vals := [x[1] : x in eigs];
   require forall{x : x in e_vals | x in T[1] cat T[2]}: "The eigenvalues of a must be in T.";
   require 1 in e_vals: "a must be an idempotent.";
   n := Dimension(A);
   F := BaseRing(A);
   require &+[x[2] : x in eigs] eq n: "a must be semisimple.";
   bas_plus := &cat[ Basis(Eigenspace(ad_a, lm)) : lm in T[1]];
   bas_minus := &cat[ Basis(Eigenspace(ad_a, lm)) : lm in T[2]]; 
   return Matrix(bas_change)^-1*(DiagonalJoin(IdentityMatrix(F, #bas_plus), ScalarMatrix(#bas_minus, -F!1)))*bas_change
	where bas_change := Matrix(bas_plus cat bas_minus);
	/* The matrix of the map wrt the basis bas_plus cat bas_minus is the block diagonal (I_k, -I_{n-k})*/
end intrinsic;

//================= particular case of the Monster fusion law ===========================================

intrinsic TauMapMonster(a::AlgGenElt:values := false) -> AlgMatElt
{
   For an axis a, find the corresponding tau map. Default values of alpha, beta are 1/4, 1/32.
   The user can specify values of alpha beta by giving a tuple values:=\<alpha, beta\>. No check 
   will be made that a satisfies the Monster fusion law. 
}
	
   if Type(values) eq BoolElt then
      alpha := 1/4;
      beta := 1/32;
   else
      alpha := values[1];
      beta := values[2];
   end if;
   return TauMap(a, < [1,0,alpha], [beta] >);
end intrinsic;

//=================== Find the sigma map for a Jordan axis ================================================
 
intrinsic SigmaMapMonster(a::AlgGenElt:eta := false) -> AlgMatElt
{
   Find the sigma map of a Jordan eta axis. No check that 
   a satisfies the Jordan fusion law is made. Default value of eta is 1/4.
}
   if Type(eta) eq BoolElt then
      eta := 1/4;
   else
      require eta in BaseField(Parent(a)): "The value of eta must be in the base field 
        of the parent algebra of a.";
   end if;
   return TauMap(a, < [1, 0], [eta] >);
end intrinsic;	

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+Given a matrix M for a map A->A, and a subspace U of A, not necessarily a subalgebra, +
+ find the restriction of the map to U as a dim(U)xDim(U) matrix. This requires U to be+
+ M-invariant.                                                                         +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic RestrictMapToSubspace(M::AlgMatElt, U::ModTupFld) -> AlgMatElt
{
   Let M be a matrix for a map A->A and U be a subspace of A. If U is M-invariant,
   find the restriction of the map to U as a dim(U)xdim(U) matrix.
}
   require Nrows(M) eq Ncols(M): "The given matrix is not square";
   require Nrows(M) eq Degree(U): "The map and the space are not compatible.";
   n := Dimension(U);
   bas := Basis(U);
   bas_ims := ApplyMatrixToVectors(M, bas);
   require forall{v : v in bas_ims | v in U}: "The given space is not invariant.";
   return Matrix(Solution(BasisMatrix(U), bas_ims));
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given a vector space V over a field F, a number lambda in F, and a matrix M representing a map phi: V-->V, find the  +
+ lambda eigenspace of V as Degree(V)-long vectors.                                                                    +
+                                                                                                                      +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic EigenspaceOfMap(M::AlgMatElt, V::ModTupFld, lambda::FldElt) -> ModTupFld
{
   Given a square matrix M, a vector space V such that the dimension of M is dim(V)xdim(V), and both M and V 
   are over the same field; M represents a map phi: V\-->V; together with a scalar lambda, find the lambda eigenspace 
   of V, i.e, the subspace \{v:v in V|v\^phi =lambda*v\}.
 }
   require Nrows(M) eq Ncols(M) and BaseRing(V) eq BaseRing(M): "M and V must be over the same field.";
   require Nrows(M) eq Dimension(V): "The size of M must agree with the dimension of V.";
   m := Dimension(V);
   n := Degree(V);
   F := BaseRing(V);
   t:= Cputime();
   space := Nullspace(lambda*I-M) where I is IdentityMatrix(F, m);
   vprintf Automorphisms, 1: " Degree %o eigenspace found in %o seconds\n", m, Cputime(t);
   if Dimension(space) eq 0 then
      return sub<V | [V | ]>;
   else
      return sub<V | [&+[(space.i)[j]*bas[j] where bas is Basis(V) : j in [1..m]] : i in [1..k]]> where k is Dimension(space);
   end if;
end intrinsic;	

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given a vector space V of dimension m and a square matrix M of dimension m over the same field as V, construct the map +
+ phi: V-->V that is represented by the matrix M with respect to a basis of V.                                           +
+                                                                                                                        +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic MapFromMatrix(M::AlgMatElt, V::ModTupFld) -> Map
{
   For a vector space V of dimension m over a field F, together with a square matrix M in F\_n, find the map 
   phi:V\-->V which is represented by M relative to a basis of V.
}
   require Nrows(M) eq Ncols(M) and BaseRing(V) eq BaseRing(M): "M must be square and over the same field as V.";
   require Nrows(M) eq Dimension(V): "The size of M must equal the dimension of V.";
   m := Dimension(V);
   return hom<V -> V | [ <bas[i], &+[M[i][j]*bas[j] : j in [1..m]]> : i in [1..m]] > where bas is Basis(V);
   /* Here it is more prudent to use Basis instead of .i in case of V generated by non-standard bases.*/
end intrinsic;

/*============================================ Find form, check, and evaluate form =========================================*/

//=============================== Check that a form is associating =========================================================

intrinsic IsAssociatingForm(A::AlgGen, form::AlgMatElt) -> BoolElt
{  Check if the bilinear form "form" is associating for the algebra A.
    Assumes that the algebra is commutative (since axial algebras are).  }
   n := Dimension(A);
   require Nrows(form) eq n and Ncols(form) eq n: "The given form is not compatible"*
   " with the given algebra.";
   require not IsZero(form): "form must be nonzero.";
   t0 := Cputime();
   prods := BasisProducts(A);
   vprintf Automorphisms, 1: "The products of basis elements accessed in %o seconds.\n", Cputime(t0);
   t0 := Cputime();
   products_under_form_left := [ApplyMatrixToVectors(form, prods[i]) : i in [1..n]];
   vprintf Automorphisms, 1: "The values (a_ia_j, a_k) evaluated in %o seconds.\n", Cputime(t0); 
   if IsSymmetric(form) then
       products_under_form_right := products_under_form_left;
   else
      t0 := Cputime();
      products_under_form_right := [ApplyMatrixToVectors(Transpose(form), prods[i]) : i in [1..n]];
      vprintf Automorphisms, 1: "Values (a_i, a_j*a_k) computed in %o seconds\n", Cputime(t0);
   end if;
    // perform the check
   triples := [<i, j, k> : i, j, k in [1..n] | i le j and (prods[i][j] ne 0 or prods[j][k] ne 0) and ( not (#{i, j, k} eq 1 ) and prods[i][i] eq A.i)];
   if exists{x : x in triples | products_under_form_left[x[1]][x[2]][x[3]] ne products_under_form_right[x[2]][x[3]][x[1]]} then
      return false;
   else
      return true;
   end if;
end intrinsic;

//=========================== Determine if an algebra A admits a form and determine such forms ==================================
intrinsic HasFrobeniusForm(A::AlgGen ) -> BoolElt, ModTupFld
 { Given an algebra A, find if it admits a Frobenius form. Return the space 
    of Frobenius forms if it exists, as well as the boolean true, false otherwise.  }
 n := Dimension(A);
 F := BaseField(A);
 if Dimension(A) eq 1 then
    return true, VectorSpace(F, 1);
 end if;
  space_initialised := false;
 /*set up system of equations for solving*/
    t0 := Cputime();
    prods := BasisProducts(A);
    /* Magma keeps the structure constants as a list of lists[[a_i*a_j:j in [1..n]] : j in [1..n]].
    Thus, the structure constants of a_ia_j are found in prods[i][j]
    */
    vprintf Automorphisms, 1: "The structure constants accessed in %o seconds\n", Cputime(t0);
    complete := false;
    triples := {<i, j, k> : i, j, k in [1..n] | i le j and (prods[i][j] ne 0 or prods[j][k] ne 0)
    and (not (#{i, j, k} eq 1 and prods[i][i] eq A.i))};// commutativity
    used_triples := {}; //reset this to zero
    // select n^2+some extra initially
    remaining_triples := triples;/*initially, but update. */
    epsilon := 5;
    m := n^2+epsilon;
    if n le 3 then
        used_triples := triples;
    else
    	repeat
       	triple := Random(triples);
	Include(~used_triples, triple);
	until #used_triples eq m;	
    end if;
    while complete eq false do
        used_triples := (IndexedSet(used_triples));
        t0 := Cputime();
        Q_L := [<(used_triples[t][1]-1)*n+l,t,(prods[used_triples[t][2]][used_triples[t][3]])[l]>
		   : l in [1..n] , t in [1..#used_triples]];
        Q_R := [<(l-1)*n+used_triples[t][3], t, (prods[used_triples[t][1]][used_triples[t][2]])[l]>
		   : l in [1..n], t in [1..#used_triples]];
        mat_L := SparseMatrix(F, n^2, #used_triples, Q_L);
        mat_R := SparseMatrix(F, n^2, #used_triples, Q_R);
	vprintf Automorphisms, 1: "Left-hand and right-hand matrices formed in %o seconds.\n", Cputime(t0);
	coeff_mat := mat_L -mat_R;
	delete mat_L;
	delete mat_R;
        t0 := Cputime();
	if not space_initialised then
	   space := Nullspace(coeff_mat);
	   space_initialised := true;
	 else
	    space meet:= Nullspace(coeff_mat);
	 end if;
	 vprintf Automorphisms, 1: "The solution space for the system found in"*
	 " %o seconds\n", Cputime(t0);
	 vprintf Automorphisms, 1: "The current memory used is %o megabytes\n", GetMemoryUsage()/(1024.0^2);
	 if Dimension(space) eq 0 then
	    complete := true;
	    return false,_;
	  end if;
	  /*check that the solution holds for all basis elements/generators.*/
          vprintf Automorphisms, 1: "checking on all triples..\n";
          for i := 1 to Dimension(space) do
            form := Matrix(F, n, n, Eltseq(space.i));
            t0 := Cputime();
	      if not IsAssociatingForm(A, form) then
                vprintf Automorphisms, 1: "Check failed, more equations required.\n";
                // update
                remaining_triples := triples diff Set(used_triples);
		used_triples := {};
		if #remaining_triples gt n^2 then
			m := n^2;
		else
			m := #remaining_triples;
		end if;
		repeat
	       	triple := Random(remaining_triples);
		Include(~used_triples, triple); 
		until #used_triples eq m;
                break i;
            end if;
            vprintf Automorphisms, 1: "Check for basis %o of the solution space "*
	    "completed in %o seconds\n", i, Cputime(t0);
        end for;
        complete := true;
    end while;
    return true, space;
 end intrinsic;

//================================== Evaluate (u, v) with respect to a form ==========================================

intrinsic FrobeniusFormAtElements(u::AlgGenElt, v::AlgGenElt, U::AlgMatElt ) -> FldElt
{ Given algebra elements u and v, together with a form U as a matrix, find ((u,v))U. }
   require Parent(u) eq Parent(v): "The given elements must be in the same algebra";
   require (Nrows(U) eq Ncols(U)) and Degree(u) eq Nrows(U) : "The form must be a square matrix compatible with the elements.";
   F := BaseRing(Parent(u)); // sometimes we enlarge the field to a function field
   require IsCoercible(F, BaseRing(U).1): " The base ring of the form must be  a subfield of the base ring of the algebra.";
   U := ChangeRing(U, F);
   return InnerProduct(u, v*U_transpose) where U_transpose := Transpose(U);// don't assume symmetry
end intrinsic; 

//============================= Particular case where u=v, so one less argument=========================================
intrinsic LengthOfElement(u::AlgGenElt, U::AlgMatElt) -> FldElt
{ Given an algebra element u and a form U as a matrix, find ((u,u))U. }
   return FrobeniusFormAtElements(u, u, U);
end intrinsic;

/*=======================================================================
* Suppose that an algebra A has a form U. Let B be a subalgebra of A.   +
*This function produces the form restricted to B.                       + 
========================================================================*/
intrinsic RestrictedForm(U::AlgMatElt, B::ModTupFld) -> AlgMatElt
{
   Given a subpace B of an algebra A admitting a form U, restrict the form to B.
}
   require Nrows(U) eq Ncols(U): "The form must be a square matrix";
   require Degree(B) eq Nrows(U): "B must be a subspace of the parent algebra"; 
   UU := ChangeRing(U, BaseRing(B));
   bas := Basis(B);/*Issues with use of B.i when B is generated by some things.*/
   bas_ims := ApplyMatrixToVectors(Transpose(UU), bas);
   arr := [[InnerProduct(bas[i], bas_ims[j] ) : j in [1..Dimension(B)]] : i in [1..Dimension(B)]];
   return Matrix(BaseRing(B), arr);
end intrinsic;

/*=========================================== Idempotent utilities=========================================================*/


//================================ check if an element is idempotent=======================================================

intrinsic IsIdempotent(u::AlgGenElt) -> BoolElt
{  check if an algebra element is an idempotent. } 
   require u ne 0 : "The element must be nonzero";
   return (u*u eq u) select true else false;
end intrinsic;

//================================= GetIdempotent ideal ===================================================================


intrinsic GetIdempotentIdeal(A::AlgGen, U::ModTupFld: length := false, form := false, one := false, extra_rels := [],
		   subalgebra := false) -> SetIndx
  {
  Given an algebra A and a subspace (not necessarily a subalgebra) U, form the ideal for finding all the idempotents of A contained in U.
  
  Optional arguments:
    length - requires the length of the idempotents to be as given
    form - the Frobenius form
    one- the identity of A. 
    subalgebra- a boolean indicating whether U is a subalgebra or not. User must make sure it is if turned to true.
    extra_rels - require the idempotent to satisfy extra relation(s).  These are given by multivariate polynomials
in dim(U) variables corresponding to the basis of U.
    }
  n := Dimension(A);
  m := Dimension(U);
  F := BaseField(A);
  R := PolynomialRing(F, m);/*Set up F[x_1,x_2,...,x_m].*/
  bas := [A!v:v in Basis(U)];

  require U subset VectorSpace(A) and Dimension(U) ne 0: "U must be a non-zero subspace of A";
  t0 := Cputime();
  prodsU := BatchMultiply(bas, bas);
  vprintf Automorphisms, 1: "products of basis vectors of the subspace found in %o seconds\n", Cputime(t0);
  // For a general idempotent $u$ in $U,$ we can write $u=\sum_{i=1}^m x_iu_i$, the $x_i$ to be found,
  // and $(u_1, u_2,\ldots , u_m)$ a basis for $U$. For $1\leq i,j \leq m,$ $u_iu_j=\sum_{l=1}^n \gamma_{ijl} a_l$ 
  // where $(a_1, a_2, \ldots , a_n)$ is a basis for $A$.	(We do not assume that $U$ is a subalgebra.) Then
  //$$u^2=\sum_{i=1}^m x_i^2\gamma_{iil}+2\left(\sum_{i=1}^{m-1}\sum_{j=i+1}^mu_iu_j\right)=
  //\sum_{i=1}^{m-1}\sum_{j=i+1}^m\sum_{l=1}^n \gamma_{ijl}x_ix_ja_l.$$
  // Using independence of the $a_l$, changing the order of summation, we have for each $l\in \{1,2,\ldots, n\}.$
  // $$0=\sum_{i=1}^mx_i^2\gamma_{iil}+2\left(\sum_{i=1}^{m-1}\sum_{j=i+1}^m\gamma_{ijl}x_ix_j\right)-\sum_{i=1}^m\beta_{il}x_i,$$
  // where $u_i=\sum_{i=1}^n\beta_{il}a_l$ so $u=\sum_{i=1}^nx_iu_i=\sum_{l=1}^n\sum_{i=1}^m\beta_{il}x_ia_l.$

  relations := { R| };
  t := Cputime();
  if subalgebra eq true then
     coords := Solution(BasisMatrix(U), [Vector(v) : v in prodsU]);
     for k := 1 to m do
        relation := &+[R.i^2*coords[Ind(m, i, i)][k] : i in [1..m]]+
			+2*(&+[&+[ (coords[Ind(m, i, j)][k])*R.i*R.j : j in [i+1..m]] : i in [1..m-1]])-R.k;
        Include(~relations, relation);
     end for;
     vprintf Automorphisms, 1: "The relation coming from the idempotency found in %o seconds\n", Cputime(t);
  else
     for l := 1 to n do
        relation := &+[R.i^2*(prodsU[Ind(m, i, i)])[l] : i in [1..m]]+// sum of squares
	2*((m eq 1) select R!0  else (&+[ &+[R.i*R.j*(prodsU[Ind(m, i, j)])[l] : j in [i+1..m]]: i in [1..m-1]]))-// products of distinct u_i, u_j, j >i
	&+[R.i*(bas[i])[l] : i in [1..m]];
        Include(~relations, relation);
     end for;
     vprintf Automorphisms, 1: "The relation coming from the idempotency found in %o seconds\n", Cputime(t);
  end if;
// we will change approach here and not use function field multiplication
  if #extra_rels gt 0 then //there are some extra relations provided by the user. Check that they are OK.
     require forall{ f: f in extra_rels| IsCoercible(R, f) }: "The extra relations must be in the correct"*
     " polynomial ring.";
     extra_rels := [R!f : f in extra_rels];
  end if;
 	
// Suppose that the user has a provided form and length. Check that they are in the right format. 
  if Type(length) ne BoolElt then
     require IsCoercible(F, length): "The length must be a field element.";
     if Type(form) ne BoolElt then
        require Type(form) eq AlgMatElt: "form must be a matrix.";
	require Nrows(form) eq Ncols(form) and Nrows(form) eq n: "form must be a square"*
	"matrix compatible with the algebra";
     end if;
     if Type(form) eq BoolElt then
        bool, form := HasFrobeniusForm(A);
        if not bool then
           error "form is not given so concept of length does not make sense";
        else
           if Dimension(form) gt 1 then
           printf "The form is not unique, the first one will be used\n.";
	end if;
        form := Matrix(F, n, n, Eltseq(form.1));
        lm := LengthOfElement(A.n, form);
        assert lm ne 0;
        form := 1/lm*form;
     end if;
  end if;
  // We add the quadratic length requirement $(u,u)-l=0$ where l is the given length
  // Suppose that l is the user supplied length, so we want to find idempotents $u$ such that 
  // $(u,u)-l=0$. Recall that $u=\sum_{i=1}^mx_iu_i$. We can work out that this condition
  // gives the following equation by repeatedly using the linearity of the form (,):
  // $$0=\sum_{i=1}^n(u_i, u_i)x_i^2+2\left(\sum_{i=1}^{m-1}\sum_{j=i+1}^m(u_i, u_j)x_ix_j\right)-l$$
  t0 := Cputime();
  extra_rels cat:= [&+[LengthOfElement(bas[i], form)*(R.i)^2 : i in [1..m]]+
  2*((m eq 1) select 0 else &+[&+[ FrobeniusFormAtElements( bas[i], bas[j], form)*R.i*R.j : j in [i+1..m]] : i in [1..m-1]])-length];
  vprintf Automorphisms, 1: "The quadratic length relation found in %o seconds \n", Cputime(t0);
  // Now suppose that a one is provided by the user. First check that it is indeed a one.
  if Type(one) ne BoolElt then
     require Type(one) eq AlgGenElt: "one must be an algebra element.";
     require BatchMultiply(Basis(A), one) eq Basis(A): "one must be the algebra identity";
     // when we get here then we have a bonafide one. Use the linear length condition
     // to extra_rels. Here we have $(u,u)=(u, u\mathbbm{1}_A)=(uu,\mathbbm{1}_A)=(u, \mathbbm{1}_A)$. 
     // This gives us the equation $$0=l-\sum_{i=1}^m(u_i, \mathbbm{1}_A)x_i.$$
     t0 := Cputime();
     extra_rels cat:= [ length- (&+[FrobeniusFormAtElements(bas[i], one, form)*R.i : i in [1..m]])];
     vprintf Automorphisms, 1: "The linear length relation found in %o seconds \n", Cputime(t0);
  else// user did not provide identity. Check if it exists.
     t0 := Cputime();
     bool, one := HasOne(A);
     if bool eq true then
        //add the linear length condition (u,one)-l=0 to extra_rels
        extra_rels cat:= [length-(&+[FrobeniusFormAtElements(bas[i], one, form)*R.i : i in [1..m]])];
        vprintf Automorphisms, 1: "The identity and the linear length relation found in %o seconds \n", Cputime(t0);
     end if;
  end if;
 end if;
 // At this stage everything extra has been added to extra_rels
 return ideal< R | Set(rels cat extra_rels) > where rels := SetToSequence(relations);
end intrinsic;

//===========================================Find all idempotents in a linear space W of A===================================
intrinsic FindAllIdempotents(A::AlgGen, U::ModTupFld: length := false, form := false, one := false, extra_rels := []) -> SetIndx
{ Given an algebra A and a subspace (not necessarily a subalgebra) U, find all idempotents of A contained in U
  Optional arguments:
  length- requires the length of the idempotents to be given,
  form- the Frobenius form;
  one- the identity od A;
  extra_rels- require the idempotents to satisfy extra relation(s). These are given as multivariate
  polynomials in dim(U) variables.
  }
 t0 := Cputime();
 I := GetIdempotentIdeal(A, U: length:= length, form:=form, extra_rels := extra_rels);
 vprintf Automorphisms, 1: "The ideal has been set up in %o seconds.\n", Cputime(t0);
 t0 := Cputime();
 Groebner(I);
 vprintf Automorphisms, 1: "The Groebner basis has been computed in %o seconds.\n", Cputime(t0); 
 dim := Dimension(I);
 if dim gt 0 then
    vprintf Automorphisms, 1:  "the ideal is positive dimensional";
    return "fail";
 end if;
 F := BaseRing(A);
 m := Dimension(U);
 bas := Basis(U);
 t := Cputime();
 var_size_alg := VarietySizeOverAlgebraicClosure(I);
 vprintf Automorphisms, 1: "The size of the variety over the algebraic closure computed in %o seconds\n", Cputime(t);
 t0 := Cputime();
 var := Variety(I);
 vprintf Automorphisms, 1: "The variety over the ground field found in %o seconds\n", Cputime(t0);
 if #var lt var_size_alg then
    FClos := AlgebraicClosure(F);
    J := ChangeRing(I, FClos);
    t0 := Cputime();
    Groebner(J);
    vprintf Automorphisms, 1: "The Groebner basis for the variety over the algebraic closure found in %o seconds.\n", Cputime(t0);
    var := Variety(J);
    vprintf Automorphisms, 1: "The variety over the algebraic closure found in %o seconds.\n", Cputime(t0);
    AClos := ChangeRing(A, FClos);
    return {@ &+[x[i]*(AClos!bas[i]) : i in [1..m]] : x in var @};
 else
    return {@ A!(&+[x[i]*bas[i] :  i in [1..m]]) : x in var @};
 end if;
end intrinsic;

//============================ Find all idempotents in a coset u+W==================================
intrinsic FindAllIdempotentsInCoset(u::AlgGenElt, W::ModTupFld: length := false, form := false) -> SetIndx
{  Find all idempotents in the coset u+W where W is asubspace of the algebra containing u }
  A := Parent(u);
  require W subset VectorSpace(A)  and Dimension(W) gt 0: "The linear space must be a nonzero subspace of the parent algebra.";
  F := BaseRing(A);
  m := Dimension(W);
  n := Dimension(A);
  bas := Basis(W); /* This is w_1, w_2,\ldots, w_m.*/
  prods := BatchMultiply(L, L) where L:= [A!v : v in bas]; /*products w_iw_j 1\leq i\leq j \leq m*/
  R := PolynomialRing(F, m);
  AA := BasisMatrix(W);
  B := AdMat(u);
  t_0 := Cputime();

  List_prods:=[(&+[prods[Ind(m, i, i)][k]*R.i^2 : i in [1..m]])+2*((m eq 1)  select 0 else &+[&+[R.i*R.j*prods[Ind(m, i, j)][k] :
  j in [i+1..m]] : i in [1..m-1]])+2*(&+[B[l,k]*(&+[AA[i,l]*R.i : i in [1..m]]) : l in [1..n]])+
  (&+[-AA[i,k]*R.i : i in [1..m]])+(u*B)[k]-u[k] : k in [1..n]];

 /* We now deal with the length Condition here*/
 if Type(length) eq BoolElt then
   I := ideal<R | Set(List_prods)>; // do this if there is no length restriction
   vprintf Automorphisms, 1: "ideal set up in %o seconds.\n", Cputime(t_0);
 end if;
 if Type(length) ne BoolElt then // length restriction here
   require IsCoercible(F, length): "The length must be over the same field as the arguments.";
   if Type(form) ne BoolElt then
     require Type(form) eq AlgMatElt: "form must be a matrix.";
     require BaseRing(form) eq F and Nrows(form) eq Ncols(form): "The form must be a square matrix over the base ring of the inputs.";
   else
      bool, form := HasFrobeniusForm(A);
      if bool eq false then
         printf "The concept of length is not defined if there is no form";
         return "fail";
      end if;
      // The algebra may admit multiple forms, this is better dealt with outside this function
      // Even if the form is unique, it is only unique up to scaling, so some means of scaling will be needed.
      form := Matrix(F, n, n, Eltseq(form.1));
      lm := LengthOfElement(A.n, form);
      assert lm ne 0;
      form := 1/lm*form;
    end if;
    // First the quadratic length codition. We could shorten for symmetric (,)
    len_cond := [&+[&+[R.i*R.j*FrobeniusFormAtElements(A!bas[i], A!bas[j], form) : i in [1..m]] :
    j in [1..m]]+(&+[R.i*FrobeniusFormAtElements(A!bas[i], u, form) : i in [1..m]])+
    (&+[R.i*FrobeniusFormAtElements(u, A!bas[i], form) : i in [1..m]])-length+LengthOfElement(u,form)];
    vprintf Automorphisms, 1: "The length condition has been imposed.\n"; 
    // Now check if the algebra is unital
    bool, one := HasOne(A);
    if bool then
      linear_len_cond := FrobeniusFormAtElements(u, one, form)-length+(&+[FrobeniusFormAtElements(A!v, one, form)*R.(Index(bas,v)): v in bas]);
      Append(~len_cond, linear_len_cond);
    end if;
    I := ideal<R | List_prods cat len_cond>;
  end if;
  vprintf Automorphisms, 1: "ideal set up in %o seconds.\n", Cputime(t_0);
  t0 := Cputime();
  Groebner(I);
  vprintf Automorphisms, 1: "The Groebner basis formed in %o seconds.\n", Cputime(t0);
  if Dimension(I) lt 1 then
    var :=  Variety(I);
  else
    vprintf Automorphism, 1: "The ideal is positive-dimensional";
    return "fail";
  end if;
  t0 := Cputime();
  var_size_alg := VarietySizeOverAlgebraicClosure(I);
  vprintf Automorphisms, 1: "The size of the variety over the algebraic closure of the ground field"*
  " found in %o seconds.\n", Cputime(t0);
  if #var ne 0 then
    if #var eq var_size_alg then
      x_s := {@ &+[var[i][j]*bas[j] : j in [1..m]] : i in [1..#var] @}; 
      a_s := {@ u+x : x in x_s @};
      return a_s;
    else
      vprintf Automorphisms, 1: "warning, the field of definition has enlarged.";
      FClos := AlgebraicClosure(F);
      J := ChangeRing(I, FClos);
      t0 := Cputime();
      var := Variety(J);
      vprintf Automorphisms, 1: "The variety over the algebraic closure found in %o seconds.\n", Cputime(t0);
      AClos := ChangeRing(A, FClos);
      return {@&+[x[i]*(AClos!bas[i]) : i in [1..m] ] : x in var @};
    end if;
  else
    return {@ @};
  end if;
end intrinsic;

/*============================================ Extentions of maps ========================================================*/

intrinsic ExtendAutToMod(A::AlgGen, V::ModTupFld, M::ModTupFld, phi::AlgMatElt :module_check := true) -> BoolElt, ModTupFld
{
   Given an algebra A, a subalgebra V of A given as a linear space, a linear
   space M of A which is a module of V via multiplication, and a matrix phi
   representing a map V\-> V with respect to an echelonised basis of V,
   determine if phi  induces a map on M. Return a boolean value and a vector
   space of degree \(Dimension\(V\)\)\^2 where each basis vector is a
   concatenation of rows of a matrix representing the induced map, relative to an echelonised basis of M.
}
   require V subset V_A and M subset V_A where V_A := VectorSpace(A): "V and M must be subspaces of A.";
   if module_check eq true then
      require forall{v : v in BatchMultiply([A!w : w in Basis(V)], [A!w : w in Basis(M)]) | v in M } : "M must be a module for V.";
   end if;
   // The check that V is indeed a subalgebra is irrelevant here.
   F := BaseField(A);
   k := Dimension(V);
   m := Dimension(M);
   require Nrows(phi) eq Ncols(phi) and Nrows(phi) eq k : "The size of phi must agree with the dimension of V.";

   /*
   The idea is to solve the matrix equation $A^\prime C-CB=0$ with C a matrix of unknowns. This
   is Sylvester's equation, and could be solved using vectorisation, as
   ${\rm vec }(C)((A^\prime)^T \otimes I_m-I_m\otimes CB={\rm vec(O_m)$ but
   in practice when dimensions of the parent algebra become large, this hogs memory.
   Instead, we exploit Magma's sparse matrix machinery.*/
   found := false;
   used_inds := {};
   while #used_inds lt 2 do
      i := Random([1..k]);
      Include(~used_inds, i);
   end while;
   bas_V := [A!v : v in Basis(V)];
   bas_M := [A!v : v in Basis(M)];
   bas_Mmat := Matrix(bas_M);
    
   t0 := Cputime();
   // If phi is the matrix wrt the basis (v_1, v_2, ..., v_k), then v_i^\phi is the ith row of phi
   ads_vs := [AdMat(bas_V[i]) : i in [1..k]];
   vprintf Automorphisms, 1: "The adjoint matrices of the subalgebra bases elements found in %o seconds.\n", Cputime(t0);
   t0 := Cputime();
   vs_on_M := [ApplyMatrixToVectors(ads_vs[i], bas_M ) : i in [1..k]];// sequences [v_i*m_j : j in [1..m]] 
   vprintf Automorphisms, 1: "The adjoint actions of the bases vectors of the subalgebra acting on the module
   found in %o seconds.\n", Cputime(t0);
   t0 := Cputime();
   vs_on_Mcoeffs := [ Solution(bas_Mmat, [Vector((vs_on_M[i])[j]) : j in [1..m]]) : i in [1..k]];
   vs_on_Mmats := [Matrix(vs_on_Mcoeffs[i]) : i in [1..k]];
   vprintf Automorphisms, 1: "The coefficients of the images of bases vectors of the subalgebra acting on the module
   found in %o seconds.\n", Cputime(t0);
   
   t0 := Cputime();
   Coeff_mat := HorizontalJoin([HorizontalJoin([SparseMatrix(F, m^2, m, [<(l-1)*m+s, s, (vs_on_Mcoeffs[i])[j][l]> : s, l in [1..m]]) : j in [1..m]])-
                HorizontalJoin([SparseMatrix(F, m^2, m, [<(j-1)*m+t, s, &+[phi[i, l]*(vs_on_Mcoeffs[l])[t][s] :
						l in [1..k]]> : s, t in [1..m]]) : j in [1..m]]) : i in used_inds]);
   // NOTE the column number is s, where s is the index of the module basis element in the equations
   // coming from the linear independence of $(m_j)$
   vprintf Automorphisms, 1: "The coefficient matrix of the system of equations found in %o seconds\n", Cputime(t0);
   t0 := Cputime();
   n_space := Nullspace(Coeff_mat);
   vprintf Automorphisms, 1: " The system of equations solved in %o seconds\n", Cputime(t0);
   //The system is extremely over determined. For each $u$, we get $m^2$ equations and since
   //we have $m^2$ uknowns, this should be enough. (most of the time) 

   if Dimension(n_space) eq 0 then
      return false, _;
   end if;
   // At this stage if nothing has been returned we know ${\rm dim}(n_space) > 0$.

   vprintf Automorphisms, 1: "Space of extensions found, and is of dimension %o, now checking on all of basis vectors..\n", Dimension(n_space);
   t0 := Cputime();
   gammas := [Matrix([[(vs_on_Mcoeffs[i])[j][s] : j in [1..m]] : i in [1..k]]) : s in [1..m]];// form these from the above mats
   vprintf Automorphisms, 1: "The matrices encoding the coefficients of the module bases images under the subalgebra found in %o seconds.\n", Cputime(t0);
   
   t0 := Cputime();
   phi_gammas := [phi*gammas[i] : i in [1..m]];
   vprintf Automorphisms, 1: "The products of phi with the matrices above computed in %o seconds.\n", Cputime(t0);
   while not found do
      fails := [];
      for l in [1..Dimension(n_space)] do
         t0 := Cputime();
         psi := Matrix(F, m, m, Eltseq(n_space.l));
         if exists(i){i : i in [1..k] | exists(j){j : j in [1..m] | ((vs_on_Mcoeffs[i])[j])*psi ne
            Vector([InnerProduct((phi_gammas[s])[i], psi[j]) : s in [1..m]])}} then
            vprintf Automorphisms, 1: "Check for the map in basis %o of the extension fails for i= %o and j= %o. More equations needed.\n", l, i, j;
            vprintf Automorphisms, 1: "The check for basis element %o of the extension completed in %o seconds.\n", l, Cputime(t0);
            vprintf Automorphisms, 1: "Selecting another set of %o equations..\n", m^2;
            t1 := Cputime();
            i := Random({1..k} diff used_inds);
            Include(~used_inds, i);
            Coeff_mat := HorizontalJoin([SparseMatrix(F, m^2, m, [<(l-1)*m+s, s, (vs_on_Mcoeffs[i])[j][l]> : s, l in [1..m]]) : j in [1..m]])-
                HorizontalJoin([SparseMatrix(F, m^2, m, [<(j-1)*m+t, s, (phi_gammas[s])[i, t]> : s, t in [1..m]]) : j in [1..m]]);// could use in set up
            n_space meet:= Nullspace(Coeff_mat);
	    vprintf Automorphisms, 1: "The new system of equations solved in %o seconds and the space of extensions is now of dimension %o .\n",
	    Cputime(t1), Dimension(n_space);
            Append(~fails, l);
	    break l;
	 else
            vprintf Automorphisms, 1: "The check for basis element %o of the extension completed in %o seconds.\n", l, Cputime(t0);
         end if;
      end for;
      if IsEmpty(fails) then
         found := true;
      end if;
   end while; 
   return true, n_space;
end intrinsic;
//================================ Extend an injective map V -> A to an automorphism of A if possible ======================

intrinsic ExtendMapToAlgebraAutomorphism(input::SeqEnum[AlgGenElt], images::SeqEnum[AlgGenElt]: check_automorphism := true,
generators := Basis(Parent(input[1])), form := false) -> BoolElt,AlgMatElt
{
   Given two indexed sets of axial algebra elements, the first with preimages and the second containing the corresponding images, 
   extend the map as far as possible. If the map extends to the whole algebra, return true and a matrix that gives a multiplicative map A->A
   where A is the axial algebra in question. If not, return false and the maximum subalgebra (as a vector space) to which the map extends.	
}
   require #input eq #images: "The lengths of the input and output lists must be  equal.";
   A := Parent(input[1]);
   require images[1] in A: "Both the preimages and images must be in the same algebra.";
   A_W := VectorSpace(A);
   require IsIndependent(input): "The input list must be independent.";
   require IsIndependent(images): "The images list must be independent.";
   dim := Dimension(A);
   if not ISA(Type(form), BoolElt) then
      require Type(form) eq AlgMatElt  and (Nrows(form) eq Ncols(form)): "The form must be in the form of a square matrix.";
      require Nrows(form) eq dim: " The form must be compatible with A.";
      require forall{ i : i in [1..#input] | LengthOfElement(input[i], form) eq LengthOfElement(images[i], form) } :
	"Every element must be mapped to another element of the same length.";
      // other checks for preservation
   end if;
   closed := 0;
   if input eq images then /* if the original map is the identity map this is equivalent to finding a subalgebra. */
      subalgebra_mode := 1;
   else
      subalgebra_mode := 0;
   end if;
   F := BaseField(A);
   lst := input;
   ims := images;
   V := sub<A_W | [Vector(v) : v in lst] >;
   W := sub<A_W | [Vector(x) : x in ims]>;
   // Our map phi is V--> W with the bases in V and W initially being resp inputs and images.
   t0 := Cputime();
   phi := hom< V -> W | [<lst[i], ims[i]> : i in [1..#lst]]>;
   vprintf Automorphisms, 1: "The map form of the mapping formed in %o seconds.\n", Cputime(t0);
   t0 := Cputime();
   require Dimension(Kernel(phi)) eq 0: "The map must be injective.";
   vprintf Automorphisms, 1: "The injectivity check performed in %o seconds.\n", Cputime(t0);
   m := 1; //For m-closure
   current := [1, #lst];
   new := [1, #lst];
   old_domain := V;
   while closed eq 0 do
      t0 := Cputime();
      if not current eq new then
         vprintf Automorphisms, 1: "current is %o, new is %o\n", current, new;
	 prods := BatchMultiply(lst[[current[1]..new[1]-1]], lst[[new[1]..new[2]]]) cat
		BatchMultiply(lst[[new[1]..new[2]]], lst[[new[1]..new[2]]]);
	 if subalgebra_mode eq 1 then
	    im_prods := prods;
	 else
	    im_prods := BatchMultiply(ims[[current[1]..new[1]-1]], ims[[new[1]..new[2]]]) cat
			BatchMultiply(ims[[new[1]..new[2]]], ims[[new[1]..new[2]]]);
	 end if;
	 vprintf Automorphisms, 1: "products of both inputs and images computed in %o seconds\n", Cputime(t0);
      else
	 prods := BatchMultiply(lst, lst);
	 if subalgebra_mode eq 1 then
	    im_prods := prods;// images and inputs coincide
	 else
	    im_prods := BatchMultiply(ims, ims);
	 end if;
	 vprintf Automorphisms, 1: "products of both inputs and images computed in %o seconds\n", Cputime(t0);
      end if;
      V +:= sub<A_W | [Vector(v) : v in prods]>;
      W +:= sub<A_W | [Vector(x) : x in im_prods]>;
      n_d := Dimension(V);
                         
      if Dimension(W) ne n_d then
         print "The map cannot be extended to an algebra automorphism.";
         return false, _;
      end if;

      //extend lst to a basis of V (new) using products, and the same for ims and W.
      used_prods := [];
      used_ims := [];
      outside_prod_inds := [];
      sub_dom := sub<A_W | [Vector(v) : v in lst]>;
      for i := 1 to #prods do
         if prods[i] notin sub_dom then
	    Append(~ used_prods, prods[i]);
	    if subalgebra_mode eq 0 then //test to see if this will be worthwile
               Append(~used_ims, im_prods[i]);
	    end if;
	    sub_dom +:= sub<A_W | Vector(prods[i])>;
            Append(~outside_prod_inds, i);
	 end if;
	 if Dimension(sub_dom) eq n_d then
            break i;
	 end if;
      end for;
      if not IsEmpty(outside_prod_inds) then
         if current eq new then
            m := 2;
         elif exists{ind : ind in outside_prod_inds | ind gt current[2]*(new[2]-new[1]+1)} then
            m := 2*m;
	 else
            m := 2*m-1;
         end if;
      end if;
      lst cat:= used_prods;
      if subalgebra_mode eq 1 then //remove if no time gains
         ims := lst;
      end if;
      ims cat:= used_ims;
      if #lst eq dim then// This will prevent an unnecessary round of multiplication
         vprintf Automorphisms, 1: "Current size of used_prods is %o \n", #used_prods;
	 vprintf Automorphisms, 1: "The current counter current is %o and the new counter is %o\n", current, new;
	 vprintf Automorphisms, 1: "multiplication is now closed with minimum %o-closure \n", m;
	 closed +:= 1;
      end if;
      if #used_prods eq 0 then
         closed +:= 1;
	 vprintf Automorphisms, 1: "Current size of used_prods is %o \n", #used_prods;
	 vprintf Automorphisms, 1: "The current counter current is %o and the new counter is %o\n", current, new;
	 vprintf Automorphisms, 1: "multiplication is now closed with minimum %o-closure \n", m;
      else
         /*update new and current.*/
	 old_domain := sub<A_W | [Vector(v) : v in lst]>;	
	 new := [current[2]+1, #lst];
	 current := [1, #lst];
	 vprintf Automorphisms, 1: "current dimension is %o\n", #lst;
	 vprintf Automorphisms, 1: "Current size of used_prods is %o \n", #used_prods;
      end if;
   end while;
   vprintf Automorphisms, 1: "now exited the while loop\n"; 
	if #lst lt dim then
		return false, V;
	end if;
	bas_mat := Matrix([Vector(v) : v in lst]);
	coordinates := Solution(bas_mat, [Vector(ims[i]) : i in [1..dim]]);
	phi_mat := Matrix( coordinates);
	phi_mat := bas_mat^-1*phi_mat*bas_mat;
        if check_automorphism eq true and #lst eq dim then
	       bool := IsAutomorphism(A, phi_mat: generators:= generators);
               if bool then
	            return true, phi_mat;
               else
      	            print "The map is not automorphic";
                    return false, _;
               end if;
       elif check_automorphism eq false and #lst eq dim then
		return true, phi_mat;
      end if;
end intrinsic;

/*============================================ Find Jordan axes, twins ===================================================*/
//==================================== Annihilator Of Space =============================================================

intrinsic AnnihilatorOfSpace(A::AlgGen, U::ModTupFld) -> ModTupFld
{
	Given an algebra A and a subspace (not necessarily a subalgebra) U of A, find annU, the space \{a: a in A|aU=0\}.
}
	require U subset VectorSpace(A): "U must be a subspace of A.";
	bas_U := Basis(U);
	/* Let $a_1, a_2,\ldots , a_n$ be a basis for $A$, and $u_1, u_2, \ldots, u_m$ be a basis for $U$. 
	Let $x=\sum_{i=1}^n=x_ia_i$ be a general vector in ${\rm ann}U=\{a\in A| aU=0\}.$ Then for all 
	$u_j$ in the basis, $xu_j=0$, that is, $0=\left(\sum_{i=1}^nx_ia_i\right)u_j=\sum_{i=1}^nx_i(a_iu_j).$ 
	Notice here that $a_iu_j=u_j^{{\rm ad}_{a_i}}.$ We will use the notation $a_iu_j=\sum_{k=1}^n=\alpha^i_{jk}a_k$ 
	with the superscript indicating that $a_i$ is acting on $u_j$, $j$ being the first subscript. Then we get the 
	following system of equations which we need to solve: $(0~ 0\ldots~ 0)=(x_1~ x_2\ldots ~x_n) [\alpha^i_{jk}]$ 
	which expands as (0 0...0)=(x_1 x_2... x_n)  [a^1_{j1} a^1_{j2}...a^1_{jn}]
						     [a^2_{j1} a^2_{j2}...a^2_{jn}]
						      .        .       ... .
						      .        .       ... .
						      .        .       ... .
						     [a^n_{j1} a^n_{j2}... a^n_{jn}] 
	where each row of the matrix is ${\rm ad}_{a_i}(u_j)$. The system is massively overdetermined, and we could choose 
	only two $u_j$s and still be fine, but the time taken is small and space is ridiculously low so that the extra work is 
       not worth it.*/
       n := Dimension(A);	
	ad_mats :=[ Matrix(bas_prods[i]): i in [1..n]] where bas_prods := BasisProducts(A);
	return Nullspace(Matrix([&cat[Eltseq(v) : v in ApplyMatrixToVectors(ad_mats[i], bas_U) ] : i in [1..n]]));
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function determines the fixed subalgebra of a given matrix group for a particular algebra A. For efficiency, give the              +
+ fewest possible number of generators of the group. The function will return the fixed subalgebra in vector space form.                  +
+                                                                                                                                         +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 
intrinsic FindFixedSubalgebra(A::AlgGen, lst::SeqEnum[AlgMatElt]) -> ModTupFld
{
   Given an algebra A and a list of automorphisms that generate the known automorphism group (containing Miy(A)) of A, 
   find the fixed subalgebra, i.e., the set of all vectors which are fixed by all Miyamoto involutions or known automorphisms.
}
   require #lst gt 0: "The sequence must be non-empty";
   dim := Dimension(A);
   require Nrows(lst[1]) eq Ncols(lst[1]) and Nrows(lst[1]) eq dim: "The elements of the sequence must be square matrices of the same dimension as A";
   require forall{ x : x in lst | IsInvertible(x)} : "Automorphisms must be invertible"; // Possibly make this optional
   return Nullspace(HorizontalJoin([ lst[i]-Id : i in [1..#lst]])) where Id := IdentityMatrix(BaseRing(A), dim);	
end intrinsic; 
/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Find all Jordan axes of type 1/4.                                                                                                       +
+                                                                                                                                         +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic JordanAxes(A::AlgGen,gens::SeqEnum[AlgMatElt] : form := false) -> SetIndx
{
   Let A be an algebra whose known automorphism group has generators gens (as a matrix group), find all Jordan 1/4 axes. 
   It is the user's responsibility to check that the matrices in gens are indeed automorphisms using IsAutomorphic.
}
	
   fix := FindFixedSubalgebra(A, gens);
   idemps := FindAllIdempotents(A, fix : form := form, length := 1) join FindAllIdempotents(A, fix : form := form, length := 2);
   /* we have proved that if j is a jordan axis, then <<a,j>> is 2A or 2B. If 2A, then (j,j) must equal (a,a)=1 since automorphisms permute axes and 
   preserve length. If 2B, the identity has length 2 and could possibly be an imprimitive axis of jordan type in A. Notice that the length condition 
   eliminates 0_A and 1_A automatically.*/
   return {@x : x in idemps | IsJordanAxis(x)@};
end intrinsic;

//============================== check that an axis is Jordan ====================================================================
intrinsic IsJordanAxis(a::AlgGenElt: eta := 1/4) -> BoolElt
{
   Given an algebra element a, determine if it is a Jordan type eta axis. The default vaue 
   of eta is 1/4.
}
   require eta in BaseField(Parent(a)): "eta must be in the base field of the parent algebra.";
   require {x[1] : x in Eigenvalues(AdMat(a))} eq {1,0,eta}: "The element does not have the correct 
	eigenvalues.";
   return HasMonsterFusionLaw(a:arbitrary_parameters := <eta, 1/8*eta>);
end intrinsic;

//======================================================Machinery for twins======================================================================

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+     Given an axis a, find axes b such that tau_a= tau_b if such axes exist.                                                                 +
+                                                                                                                                             +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic FindTwins(a::AlgGenElt: form := false, one := false, fusion_values := {@1/4,1/32@}) -> SetIndx
{
   Given an axis a of Monster type (alpha,beta), find axes b different from a, such that tau_a=tau_b,
   or tau_a=sigma_b if they exist. The default values of alpha, beta are 1/4,1/32.
}
   A := Parent(a);
   F := BaseField(A);
   if fusion_values ne {@1/4,1/32@} then 
      require Type(fusion_values[1]) eq FldElt and IsCoercible(F, fusion_values[1]): "The fusion values must be in the base field of the parent algebra.";
   end if;
   alpha := fusion_values[1];
   beta := fusion_values[2];
   require HasMonsterFusionLaw(a:arbitrary_parameters := <alpha, beta>): "The input must be an axis of Monster type (alpha,beta).";
   ad_a := AdMat(a);
   eigenspace := Eigenspace(ad_a,beta);
   // First we deal with the case ${\rm dim}(A_{\beta}) >0$.
   if Dimension(eigenspace) gt 0 then
      ann := AnnihilatorOfSpace(A, eigenspace);
      return {@ x : x in possibles | x ne a and HasMonsterFusionLaw(x) @} where possibles := FindAllIdempotentsInCoset(a, ann
      : length :=1, form := form) join FindAllIdempotentsInCoset((alpha*beta^-1)*a,ann); 
   end if;
   // Now for the case a is a Jordan axis
   if IsJordanAxis(a: eta := alpha) then
      eigenspace := Eigenspace(ad_a, alpha);
      ann := AnnihilatorOfSpace(A, eigenspace);
      return {@ x : x in possibles | x ne a and HasJordanFusionLaw(x) @} where possibles := FindAllIdempotentsInCoset(a, ann) join
      FindAllIdempotentsInCoset(alpha^-1*beta*a, ann);
   end if;
end intrinsic;

/*===================================================== Decompositions ===================================================*/

intrinsic JointEigenspaceDecomposition(L::SetIndx[AlgGenElt]) -> Assoc
   {
   Given an indexed set of axes L = \{ a_1, ..., a_n\}, decompose the algebra into joint eigenspaces for these axes.
	  Returns an associative array where the element A_lm_1(a_1) \cap ... \cap A_lm_n(a_n) has keys give by the set of eigenvalues \{ lm_1, ..., lm_n \}.
   }
  
   /* should we check that the a_i are axes, i.e., HasMonsterFusion(a_i)? */
   decomps := AssociativeArray();
   A := Parent(L[1]);  
   eigs := [1, 0, 1/4, 1/32];
   n := #L;
   dims := [];
   ads := [AdMat(L[i]) : i in [1..n]];
   Lst := [[Eigenspace(ads[i],1) : i in [1..n]],[Eigenspace(ads[i],0) : i in [1..n]],[Eigenspace(ads[i],1/4)
           : i in [1..n]],[Eigenspace(ads[i],1/32) : i in [1..n]]];
   cart := CartesianPower([1..4],n);
   for x in cart do 
      joint_space := &meet[Lst[x[i]][i] : i in [1..n]];
      dim := Dimension(joint_space);
      if not dim eq 0 then
         Append(~dims,dim);
 	 decomps[[eigs[x[i]] : i  in [1..n]]] := joint_space;
      end if; 
   end for; 
   return decomps;
end intrinsic;

/*========================================= Find, check fusion laws ======================================================*/

intrinsic DisplayFusionLaw(fus::List) -> MonStgElt
   { Given a fusion law, display it in a table }

   values := &join{{ l : l in TupleToList(law[1])} : law in fus };
   F := Parent(SetToSequence(values)[1]);
   evals := [F | 1 ];
   if 0 in values then
      Append(~evals, 0);
   end if;
   squares := [* *];
   for x in values diff SequenceToSet(evals) do
      law := [l : l in fus | l[1] eq <x, x> ];
      Append(~squares, Sprintf("%o", law[1][2]));
   end for;
   widths := [#x : x in squares];
   m_2 := Maximum(widths);
   outside := [x : x in values | x notin evals ];
   m_1 := Maximum([#Sprintf("%o", x):x in outside]);
   for x in outside do
      m_ind := Index(widths, Minimum(widths));
      Append(~evals, outside[m_ind]);
      Remove(~widths, m_ind);
      Remove(~outside, m_ind);
   end for;// arrange eigenvalues by increasing width of x*x
   strings := [];
   m := m_2+2;
   Append(~strings, &*[Sprintf("%o", " ") : i in [1..m_1-1]] cat "*|" cat &*[Sprintf("%"*Sprintf("%oo",m), x) : x in evals]);
   Append(~strings, &*[Sprintf("%o", "=") : i in [1..m_1+1+(#evals)*m]]);
   for x in evals do
      stg := Sprintf("%"*Sprintf("%oo", m_1), x)*"|";
      for i:=1 to #evals do
         if not exists(law){l : l in fus| <x, evals[i]> eq l[1]} then
 	   law := [l : l in fus | l[1] eq <evals[i], x>][1];
  	 end if;
 	 stg cat:= Sprintf("%"*Sprintf("%oo", m), law[2]);
      end for;
      Append(~strings, stg);
   end for;
   return &*[Sprintf("%o\n", stg) : stg in strings];
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an idempotent a in an axial algebra, we wish to find out if a satisfies a fusion law.       +
+                                                                                                   +
+ FindFusion Alg -->2^X, where X:=Spec(a).                                            	            +
+                                                                                                   +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic FindFusionLaw(a::AlgGenElt) -> SeqEnum /*V is a subspace which could be A.*/
{
   Given an algebra A, and an algebra element a, determine if a satisfies a fusion law in A.
}
   A := Parent(a);
   require a ne  0: "a must be nonzero";	
   require a*a eq a: "The given element is not an idempotent";
   n := Dimension(A);
   F := BaseField(A);
   W := VectorSpace(A);
   eigs := Eigenvalues(AdMat(a));
   fus := [* *];
   eigs := SetToSequence(eigs);
   evals := [eigs[i][1] : i in [1..#eigs]];
   mults := [eigs[i][2] : i in [1..#eigs]];
   require &+[x : x in mults] eq n: "The given element is not  semisimple";
   ord_eigs := [F | 1]; 
   ord_mults := [x[2]] where x is [y : y in eigs|y[1] eq 1][1];
   if 0 in evals then
      Append(~ord_eigs, F!0);
      ind := Index(eigs ,x) where x is [ y : y in eigs | y[1] eq 0][1];
      Append(~ord_mults, mults[ind]);
   end if;
   for i := 1 to #evals do
      if evals[i] notin ord_eigs then
         Append(~ord_eigs, evals[i]);
	 Append(~ord_mults, mults[i]);
      end if;
   end for;
   for j := 1 to #evals do
      for k := j to #evals do
         ind := Ind(#evals , j, k);     
         fus[ind] := [*< ord_eigs[j], ord_eigs[k] >, [ ]*];
      end for;
   end for;/*at this stage fus will have <<\mu,\lambda>,[]> for each fusion rule.*/
   Id := IdentityMatrix(F, n);
   ad_mat := AdMat(a);
   Projs := [ &*[(ad_mat-ord_eigs[j]*Id) : j in [1..#eigs] | j ne i] : i in [1..#ord_eigs]];
   //  the normalization by dividing introduces nasty coefficients
   bas := Basis(A);

   t0 := Cputime();
   Splits := [ ApplyMatrixToVectors( Projs[i], bas) : i in [1..#Projs] ];// list of lists, each a list of projections of a_i to some space
   splits := [ [Splits[i][j] : i in [1..#Splits]] : j in [1..n]];
   vprintf Automorphisms, 1: "The components of each basis element found in %o seconds\n", Cputime(t0);
   // we will only use a fraction of the splits, test for satisfication of the found 
   // fusion law over the entire A and stop if satisfied.

   count := 1;
   fusion_law_found := false;
   used_inds := { };
   k := Floor(n/10);// we will use ten percent of the splits to begin with.
   if n lt 10 then// Sometimes if only one basis vector is used there are lots of blank values
      k := n;
   end if;
   ordinals := ["first", "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth", "ninth", "tenth"];
   while fusion_law_found eq false do
      if count le 9 then
         new_inds := {};
	 repeat
	 i := Random({1..n} diff used_inds);
         Include(~new_inds, i);
	 until #new_inds eq k;
	 used_inds join:= new_inds;
	 // Add laws to fus using new_inds, then test on $\{1,\ldots, n\}$.
      else
         new_inds := {1..n} diff used_inds;
	 // Add laws to the fusion law and automatically set fusion_law_found to true;	
      end if;
      for i in new_inds do
         prods := BatchMultiply(splits[i], splits[i]);
         projs_prods := [ApplyMatrixToVectors(Projs[j], prods) : j in [1..#Projs]];
	 for s -> prod in projs_prods do
	    for t -> prod_s in prod do
	       if ((prod_s ne 0) and (ord_eigs[s] notin fus[t][2])) then
	          Append(~fus[t][2], ord_eigs[s]);
	       end if;
	    end for;
	 end for;
      end for;
      vprintf Automorphisms, 1: "The fusion law for the %o random ten percent of the basis elements"*
      " found in %o seconds\n", ordinals[count], Cputime(t0);
      if count le 9 then
         t0 := Cputime();
         fusion_law_found := SatisfiesFusionLaw(a, fus);
	 vprintf Automorphisms, 1: "The fusion law found checked on all basis elements in %o seconds\n", Cputime(t0);
	 count +:= 1;
      else
         fusion_law_found := true;
      end if;
   end while;	
   return fus;
end intrinsic;

declare verbose Fusion_check,1;

intrinsic SatisfiesFusionLaw(a::AlgGenElt, fus::List) -> BoolElt
{ For an algebra element a, and a fusion law "fus", check if a satisfies fus }
  A := Parent(a);
  n := Dimension(A);
  require times(a, a) eq a: "The first argument must be an idempotent.";
  ad_a := AdMat(a);
  fus_values := &join{ {l : l in law[1]} : law in fus };

  //This gives the fusion values if fus is the fusion law.
  eigs_ad := Eigenvalues(ad_a);
  require forall{ lm : lm in eigs_ad|lm[1] in fus_values }: "The values in the fusion law must"*
  " be eigenvalues of the adjoint action of the first argument.";

  require &+[val[2] : val in eigs_ad] eq n: "The adjoint of the first argument is not semisimple.";
  e_vals := fus_values;
  bases := AssociativeArray();
  for lm in e_vals do
    bases[lm] := [A!v : v in Basis(Eigenspace(ad_a, lm))];
  end for;
  if #bases[1] eq 1 then // a primitive
	useful_fus := [* law : law in fus| 1 notin {l : l in law[1]} *];
      // Here say $A_1(a)= <a>. Then for any $\lambda$, and $v\in A_{\lambda}(a)$ and $u\in A_1(a)$,
      // we have $u = ca,~ c\in F.$ Thus, $uv=(ca)v=c(av)=c(\lambda v)$.
      // Therefore, $a(uv)=a((c\lambda)v)=\lambda c(av)=\lambda (ca)v=\lambda uv$. So $uv\in A_{\lambda}(a)$.
      // This means that in this case we need not check the rules $1\ast \lambda$.
  else
	useful_fus := fus;
  end if;
  // I need the various projections to the respective spaces
  I_n := IdentityMatrix(BaseField(A), n);
  t0 := Cputime();
  // the projections/annihilators of each eigenspace
  space_ann := AssociativeArray();
  for lm in e_vals do
    space_ann[lm] := ad_a-lm*I_n;
  end for; 
  vprintf Fusion_check,1: "The projection matrices found in %o seconds.\n", Cputime(t0);
  // Now iterate over the useful fusion laws
  // remember that possibly lm*mu ={} so take care of this, also, some 
  // eigenspaces are possibly zero, but this has been averted by using ordered_eigs 
  // based on the actual eigenvalues of ad_a
 
  for law in useful_fus do
    lm := law[1][1];
    mu := law[1][2];
    if not ((#(bases[lm]) eq 0) or (#(bases[mu]) eq 0)) then
        t0a := Cputime();
        prods := BatchMultiply(bases[lm], bases[mu]);
        vprintf Fusion_check, 1: "products of vectors from the respective eigenspaces found in %o seconds.\n", Cputime(t0a);
        t0 := Cputime();
        if IsEmpty(law[2]) then
          bool := (Set(prods) eq {0});
          if not bool then
            return false;
            vprintf Fusion_check, 1: "law %o*%o = %o checked in %o seconds.\n", law[1][1], law[1][2], law[2], Cputime(t0);
          end if;
          vprintf Fusion_check, 1: "law %o*%o = %o checked in %o seconds.\n", law[1][1], law[1][2], law[2], Cputime(t0);
        elif not IsEmpty(law[2]) then
          t0 := Cputime();
          proj := &*[ space_ann[l] : l in law[2]];
          ims := ApplyMatrixToVectors(proj, prods);
          bool := (Set(ims) eq {0});
          if not bool then
            return false; 
            vprintf Fusion_check, 1: "law %o*%o = %o checked in %o seconds.\n", law[1][1], law[1][2], law[2], Cputime(t0);
          end if;
          vprintf Fusion_check, 1: "law %o*%o = %o checked in %o seconds.\n", law[1][1], law[1][2], law[2], Cputime(t0);
        end if;
    end if;
  end for;
return true; 
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Function to check if an idempotent satisfies the Monster M(alpha,beta) fusion law. 						          +
+           	                                                                                                                          +
+ We implement ideas from Hall, Rehren and Shpectorov's 'Universal axial algebras and a theorem of Sakuma.                                +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

/*check if the eigenvalues are in eigens, if so, check if dimensions add up.*/
intrinsic HasMonsterFusionLaw(u::AlgGenElt:arbitrary_parameters := false) -> BoolElt
{
   Check if the algebra element u satisfies the Monster M(alpha,beta) fusion law.
   The switch for arbitrary alpha and beta is off by default, when we assume (alpha,beta)
   is (1/4,1/32). Parameters:
   -arbitrary_parameters a tuple <alpha,beta>, set to false by default. 
}
   require IsIdempotent(u) : "u must be an idempotent"; 
   A := Parent(u);
   bas := Basis(A);
   n := #bas;
   F := BaseField(A);
   if Type(arbitrary_parameters) eq BoolElt then
      alpha := 1/4;
      beta := 1/32;
   else
      require Type(arbitrary_parameters) eq Tup: "The parameter must be in tuple form.";
      require arbitrary_parameters[1] in F and arbitrary_parameters[2] in F: 
      "The values alpha and beta must lie in the base field of underlying algebra.";
      alpha := arbitrary_parameters[1];
      beta := arbitrary_parameters[2];
      require <alpha, beta> notin {<0, 1>, <1, 0>} and alpha ne beta: "alpha and beta must be distinct and different from 1 and 0.";
   end if;
   fus := [* [* <1, 1>, [1]*], [*< 1, 0>, []*], [*< 1, alpha>, [alpha]*], [*<1, beta>, [beta]*], 
	 [* < 0, 0 >, [0] *], [*< 0, alpha>, [alpha]*], [*<0, beta >, [beta]*], 
	 [*<alpha, alpha>, [1, 0]*], [*< alpha, beta>, [beta]*], [*<beta, beta>, [1, 0, alpha]*] 
	*];
   return SatisfiesFusionLaw(u, fus);
end intrinsic;

intrinsic HasJordanFusionLaw(u::AlgGenElt: eta := false) -> BoolElt
{  Check whether an algebra element u is a Jordan axis of type eta. }

  require #Eigenvalues(AdMat(u)) eq 3: "The adjoint of the imput must have three eigenvalues.";
  return HasMonsterFusionLaw(u: arbitrary_parameters := (not Type(eta) eq BoolElt) select <eta, 1/8*eta> else false);
// The value 1/8*eta is just arbitrary to distinguish alpha and beta
end intrinsic; 

intrinsic HasAlmostMonsterFusionLaw(u::AlgGenElt:arbitrary_parameters := false) -> BoolElt
{
   Check if the algebra element u satisfies the almost Monster M(alpha,beta) fusion law.
   The switch for arbitrary alpha and beta is off by default, when we assume (alpha,beta)
   is (1/4,1/32). Parameters:
   -arbitrary_parameters a tuple <alpha,beta>, set to false by default. 
}
   require IsIdempotent(u) : "u must be an idempotent"; 
   A := Parent(u);
   bas := Basis(A);
   n := #bas;
   F := BaseField(A);
   if Type(arbitrary_parameters) eq BoolElt then
      alpha := 1/4;
      beta := 1/32;
   else
      require Type(arbitrary_parameters) eq Tup: "The parameter must be in tuple form.";
      require arbitrary_parameters[1] in F and arbitrary_parameters[2] in F: 
      "The values alpha and beta must lie in the base field of underlying algebra.";
      alpha := arbitrary_parameters[1];
      beta := arbitrary_parameters[2];
      require <alpha, beta> notin {<0, 1>, <1, 0>} and alpha ne beta: "alpha and beta must be distinct and different from 1 and 0.";
   end if;
   fus := [* [* <1, 1>, [1]*], [*< 1, 0>, []*], [*< 1, alpha>, [alpha]*], [*<1, beta>, [beta]*], 
	 [* < 0, 0 >, [0] *], [*< 0, alpha>, [alpha]*], [*<0, beta >, [beta]*], 
	 [*<alpha, alpha>, [1, 0, alpha]*], [*< alpha, beta>, [beta]*], [*<beta, beta>, [1, 0, alpha]*] 
	*];
   return SatisfiesFusionLaw(u, fus);
end intrinsic;
/*===================================== Find all axes in algebras of modest dimensions ==================================*/
//FindAllAxesNaive, Nuanced

intrinsic FindAllAxesNaive(A::AlgGen : form := false, length := 1) -> Setindx
{  For an algebra A of modest dimension, attempt to find all axes by finding idempotents of length 1. } 
   return { x: x in FindAllIdempotents(A, VectorSpace(A):form := form, length:= length) | HasMonsterFusionLaw(x)};
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+This is the nuanced zero subalgebra version. Take A as input, and optional parameters one, for the algebra identity, + 
+ as well as Frobenius form "form". Including these if known speeds up thngs considerably.                            +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 

IdentityLength := AssociativeArray();
types := ["2A","2B","3A","3C","4A","4B","5A","6A"];
identities_lengths := [(2^2*3)/5,2,(2^2*29)/(5*7),(2^5/11),4, 19/5,(2^5)/7,(3*17)/(2*5)];

for i in [1..#types] do
   IdentityLength[types[i]] := identities_lengths[i];
end for;

intrinsic FindAllAxesNuanced(A::AlgGen: one :=A!0, axes := [], form := IdentityMatrix(BaseField(A), Dimension(A)), Miy := false) -> SetIndx 
{
   We perform the nuanced algorithm for finding all axes in an axial algebra of modest dimension. (Works for up to ~40 on an old laptop running linux.) 
   This version only takes an algebra as input and attempts to find all axes in A. 
   Additional (optional) inputs are :
   -one, the algebra identity if it exists. The program will attempt to find this if the default is left as is, increasing run time,
   -form, the Frobenius form of A. Same as above.
   -Miy, the Miyamoto group.
 }

   require Type(one) eq AlgGenElt: "The given element is not an axial algebra element";
   if one ne A!0 then 
      require forall{i : i in [1..Dimension(A)] | one*A.i eq A.i}: "The given element is not identity";
   end if; 
   require Parent(one) eq A: "The given vector is not in the algebra";
   F := BaseField(A);
   if one eq A!0 then 
      bool_one , one := HasOne(A); // This is used in FindAllIdempotents when form is given/there
   end if;
   if IsEmpty(axes) then
      axes := [A.i : i in [1..Dimension(A)] | IsIdempotent(x) and HasMonsterFusionLaw(x) where x:= A.i ];
   end if;
   if IsIdentity(form) then
      bool_form, form := HasFrobeniusForm(A);
      if bool_form then
        form := Matrix(F, n, n, Eltseq(form.1)) where n := Dimension(A);
        lm := LengthOfElement(axes[1], form);
        form := 1/lm*form;
      else
         form := bool_form;
      end if;
   end if;
   if not Type(Miy) eq GrpMat then
      _, Miy, _, _, _ := MiyamotoGroup(axes: axes_check := false);
   end if;  
   orbs := MiyamotoOrbits(Miy, axes);
   reps := [ orbs[i][1] : i in [1..#orbs]];
   found := {@ @};
   count := 0;
   for a in reps do
      count+:= 1; 
      ad_a := AdMat(a);
      eigs := IndexedSet(Eigenvalues(ad_a));
      U := Eigenspace(ad_a, 0);
      for k in Keys(IdentityLength) do
         l := (IdentityLength[k])-1;
	 if k eq "4A" then // The 4A algebra has infinitely many idempotents 
            t0  := Cputime();
            idemps := FindAllIdempotents(A, U: length := l, form := form, one := one);
            vprintf Automorphisms, 1: "attempted to find idempotents in %o seconds.\n", Cputime(t0);
            if not Type(idemps) eq SetIndx then 
               //take any eigenspace from $\lambda ne 1$. Then u has eigenvalue $\lambda -1$.
               // Ideally we want an eigenspace as small as possible but for the cases considered 1/32 is what reduced the dimenison to zero. 
 	       W := Eigenspace(ad_a, 1/32);
               R := PolynomialRing(F, Dimension(W));
               bas_U := [A!v : v in Basis(U)];
               bas_W := Basis(W);
               t0 := Cputime();
               ads_us := [AdMat(bas_U[i]) : i in [1..#bas_U]];
               vprintf Automorphisms, 1 : "The adjoint matrices of bases elements of the zero eigenspace"*
               " subalgebra found in %o seconds.\n", Cputime(t0);
               t0 := Cputime();
               ad_us_on_W := [ApplyMatrixToVectors(ads_us[i], bas_W) : i in [1..#bas_U]];
               vprintf Automorphisms, 1: "The images of the adjoints of the zero eigenspace on the 1/32-eigenspace"*
               " found in %o seconds.\n", Cputime(t0);
               bas_Wmat := Matrix(bas_W);
               t0 := Cputime();
               coeffs := [Solution(bas_Wmat, ad_us_on_W[i]) : i in [1..#bas_U]];
               mat := Matrix([ &+[R.i*(coeffs[i])[j, l] : i in [1..#bas_U]] : j, l in [1..#bas_W]]);
               vprintf Automorphisms, 1: " The matrix of the adjoint action of u on the 1/32-eigenspace"*
               " found in %o seconds.\n", Cputime(t0);
               t0 := Cputime();
               extra := [Determinant(mat)];
               vprintf Automorphisms, 1: "The determinant of the matrix above found in %o seconds.\n", Cputime(t0);
               t0 := Cputime();
               // The relation added here is terrible, use only when the dimension of the ideal is positive.
               idemps := FindAllIdempotents(A, U: length := l, form := form, one := one, extra_rels := extra);
	       vprintf Automorphisms, 1: "idempotents found in %o seconds\n", Cputime(t0);
            end if;
         else
            t0 := Cputime();
	    idemps := FindAllIdempotents(A, U: length := l, one := one, form := form);
            vprintf Automorphisms, 1: "idempotents found in %o seconds\n", Cputime(t0);
         end if;
         vprintf Automorphisms, 1: "orbit %o %o nice idempotents found.\n", count, k;
         if not IsEmpty(idemps) then
            if IsCoercible(A, idemps[1]) then 
               for u in idemps do
                  Z := Eigenspace(AdMat(a+u), 1);
                  t0 := Cputime();
                  potential_axes := FindAllIdempotents(A, Z : length := 1, one := one, form := form);
                  vprintf Automorphisms, 1: "potential axes found in %o seconds.\n", Cputime(t0);
                  t0 := Cputime();
                  found join:= {@ x: x in potential_axes | HasMonsterFusionLaw(x) @};
                  vprintf Automorphisms, 1: "The axes in potential axes found in %o seconds.\n", Cputime(t0);
               end for;
             else
                AA := Parent(idemps[1]);
                aa := AA!a;
                for u in idemps do
                   Z := Eigenspace(AdMat(aa+u), 1);
                   t0 := Cputime();
                   potential_axes := FindAllIdempotents(AA, Z : length := 1, one := one, form := form);
                   vprintf Automorphisms, 1: "potential axes found in %o seconds.\n", Cputime(t0);
                   t0 := Cputime();
                   found join:= {@ x: x in potential_axes | HasMonsterFusionLaw(x) @}; // potential issue
                   vprintf Automorphisms, 1: "The axes in potential axes found in %o seconds.\n", Cputime(t0);
               end for;
            end if;
         end if;
         vprintf Automorphisms, 1: "The axes coming from orbit %o and B of type %o found.\n", count, k; 
      end for;
   end for;
   if #found eq #axes then
      vprintf Automorphisms, 1: "nothing new\n";
   else
      vprintf Automorphisms, 1: "%o new axes found\n", #found-#axes;
   end if;
   return found; 
end intrinsic;
/*========================================= FindShape of an algebra ====================================================*/

intrinsic FindShape(X::SeqEnum[AlgGenElt] : group := false, form := false) -> MonStgElt
{  Given a sequence X of axes generating an algebra, determine the shape.
      We do not check that the elements of X are indeed axes. The user must check. }
  A := Parent(X[1]);
  F := BaseRing(A);
  //require Subalgebra(A,IndexedSet(X)) eq VectorSpace(A): "The set X must generate the algebra.";
  require Subalgebra(IndexedSet(X)) eq VectorSpace(A): "The set X must generate the algebra.";
  if Type(group) eq BoolElt then  // Find the group
    GpPerm, group, isom, _, _ := MiyamotoGroup(X);
    group_mat := group;
    group := group@@isom;
  else // user supplied group info
    require Type(group) eq Tup and #group eq 3: "The group information must be a tuple of size three.\n";
    require Type(group[1]) eq GrpPerm and Type(group[2]) eq GrpMat: "The first two arguments of group "*
    "must be a permutation and matrix representation of the Miyamoto group, respectively.\n";
    require Type(group[3]) eq HomGrp and Domain(group[3]) eq group[1] and Codomain(group[3]) eq group[2]: 
    "The third argument of group must be a map from the permutation to the matrix representation.\n";
    group_mat := group[2];
    isom := group[3];
    group := group[1];
  end if;
  if Type(form) eq BoolElt then
    bool, form := HasFrobeniusForm(A);
    if bool eq false then
      vprintf Automorphisms,1 : "The algebra must admit a form"; 
      return "fail";
    end if;
    // scale the form to be one on axes
    form := Matrix(BaseField(A), n, n, Eltseq(form.1)) where n := Dimension(A);
    lm := LengthOfElement(X[1], form);
    form := 1/lm*form;
  end if;
  t0 := Cputime();
  pairs := Subsets(Set(X), 2);
  CartProd := CartesianProduct(pairs, group);
  f := map<CartProd -> pairs | x:->{y*(x[2]@isom) : y in x[1]}>;
  XX  := GSet(group, pairs, f);
  orbs := Orbits(group, XX);
  vprintf Automorphisms, 1 : "The number of orbits on pairs for the Miyamoto group is %o, found in %o seconds\n", #orbs, Cputime(t0);
  closures := [];
  for orb in orbs do
    pair := orb[1];
    Dihed := MatrixGroup<Dimension(A), F | [TauMapMonster(x) : x in pair]>;
    closure := &join[Vector(x)^Dihed : x in pair];
    closure := {@A!x : x in closure @};
    Append(~closures, closure);
  end for;
  sizes := [ #x : x in closures];
  vprintf Automorphisms, 1: "the sizes of the closures are %o\n", sizes;
  shapes := [];
  for i := 1 to #sizes do
    if sizes[i] in [5,6] then
      shapes[i] := Sprintf("%oA", sizes[i]);
    end if;
    if sizes[i] eq 2 and 6 in sizes then
      for six in {@x : x in closures | #x eq 6 @} do
        if exists{g : g in group_mat |closures[i] subset {@ x*g : x in six@}} then
          vprintf Automorphisms, 1 : "orbit closure %o size 2 embeds in 6 in orbit %o\n", i, Position(closures, six);
          shapes[i] := "2A";
        elif FrobeniusFormAtElements(closures[i][1], closures[i][2], form) eq 0 then
          vprintf Automorphisms, 1 : "orbit closure %o size 2 does not embed in 6 orbit %o.\n", i, Position(closures, six); 
          shapes[i] := "2B";
        else
          vprintf Automorphisms, 1 : "orbit closure %o size 2 does not embed in 6 orbit %o.\n", i, Position(closures, six);
	    shapes[i] := "2A";
        end if;
      end for;
     // check if the two embeds in a 4. Could be avoided if the check for the 4 below found ALL 2s that embed in a 4
      if exists{g : g in group_mat | exists(j){j : j in [1..#closures] | #closures[j] eq 4 and closures[i]
      subset {@ x*g : x in closures[j] @}}} then
        vprintf Automorphisms, 1: "The orbit %o of size 2 embeds in the orbit %o of size 4.\n", i, j;
      end if; 
    elif sizes[i] eq 2 and not 6 in sizes then
     // check if the two embeds in a 4. Could be avoided if the check for the 4 below found ALL 2s that embed in a 4
      if exists{g : g in group_mat | exists(j){j : j in [1..#closures] | #closures[j] eq 4 and closures[i]
      subset {@ x*g : x in closures[j] @}}} then
        vprintf Automorphisms, 1: "The orbit %o of size 2 embeds in the orbit %o of size 4.\n", i, j;
// only necessary for graph
        other_fours := [l : l in [1..#closures] | ((j ne l) and #closures[l] eq 4)
        and exists{g : g in group_mat | closures[i] subset {@x*g : x in closures[l] @}}];
        if not IsEmpty(other_fours) then
          vprintf Automorphisms, 1: " The orbit %o of size 2 also embeds in the orbits %o of size 4.\n", other_fours;
        end if;
      end if; 
      if FrobeniusFormAtElements(closures[i][1], closures[i][2], form) eq 0 then
        shapes[i] := "2B";
      else
        shapes[i] := "2A";
      end if;
    end if;
    // all the 2Ls are known now
    if sizes[i] eq 4 then
      if exists(j){j : j in [1..#closures] | sizes[j] eq 2 and exists{g : g in group_mat |
	   {@x*g : x in closures[j] @} subset closures[i] } } then 
	   vprintf Automorphisms, 1: "orbit closure %o size 2 embeds in orbit %o of size 4\n", j, i;
        if shapes[j] eq "2A" then
	  shapes[i] := "4B";
	else
	  shapes[i] := "4A";
        end if;
      else // 4L can't be determined by embedding of the 2Ls
      pair := IndexedSet(orbs[i]);
	   if FrobeniusFormAtElements(pair[1], pair[2], form) eq 1/2^5 then
	     shapes[i] := "4A";
	   else
	     shapes[i] := "4B";
           end if;	   
      end if;
    end if;
    if sizes[i] eq 3 then
      if exists(j){ j : j in [1..#closures] | sizes[j] eq 6 and  exists{g: g in group_mat|closures[i] subset
	       {@y*g:y in closures[j] @}}} then
	vprintf Automorphisms, 1 : "orbit %o of size 3 embeds in orbit %o of size 6\n", i, j;  
        other_sixes := [l : l in [1..#closures] | ((j ne l) and #closures[l] eq 6)
        and exists{g : g in group_mat | closures[i] subset {@x*g : x in closures[l] @}}];
        if not IsEmpty(other_sixes) then
          vprintf Automorphisms, 1: " The orbit %o of size 3 also embeds in the orbits %o of size 6.\n", other_sixes;
        end if;
        shapes[i] := "3A"; 
      end if;
      if not IsDefined(shapes, i) then // no embedding of the 3 in 6
        vprintf Automorphisms, 1: "orbit %o of size 3 does not embed in any 6\n",i;
        pair := IndexedSet(orbs[i][1]);
	if FrobeniusFormAtElements(pair[1], pair[2], form) eq 13/2^8 then
	  shapes[i] := "3A";
	else
	  shapes[i] := "3C";
	end if;
      end if;
    end if;
  end for;
  return &*shapes;
end intrinsic;
