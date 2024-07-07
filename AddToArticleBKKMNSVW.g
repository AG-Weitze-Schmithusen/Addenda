#In this file, we present GAP functions that we use in the article 'Arithmeticity of the Kontsevich--Zorich monodromies of certain families of square-tiled surfaces'. Most functions concern computations for origamis from the family F7 defined in the article.
# We first define the functions and then present the examples that we computed in the article

# Needed packages and files:
# 1) The GAP-packages 'Origami' and 'ModularGroup 2.0.0' from https://ag-weitze-schmithusen.github.io/Origami/.
# 2) The file arithmetic.g by ALLA DETINKO, DANE FLANNERY, AND ALEXANDER HULPKE from https://github.com/hulpke/arithmetic
#       -- this is only needed to compute the index and the level of the Kontsevich-Zorich monodromy.
# 3) This file article_KZM.g

# How to start:
# Read( "Path/arithmetic.g"), where Path is the path to arithmetic.g
# Read("Path/article_KZM.g"), where Path is the path to article_KZM.g,  e.g.: Read("/home/user/Desktop/Programs/article_KZM.g");

LoadPackage("ModularGroup");
LoadPackage("Origami");
Print("\nINFO:\n  This file presents the GAP functions used in the article [BKKMNSVW]. We use the GAP-packages [GAPOrigami] and  [GAPArithmetic].\n  You can run the functions Example1_AKZ(), Example2_AKZ(20), Example3_AKZ(20), Example4_AKZ() and Example5_KZM() to obtain the results used in the article.\n\n");
Print("\n---------------------\nBIBLIOGRAPHY:\n");
Print("  [BKKMNSVW]  E. Bonnafoux, M. Kany, P. Kattler, C. Matheus, R. Niño, M. Sedano-Mendoza, F. Valdez, G. Weitze-Schmithüsen: Arithmeticity of the Kontsevich--Zorich monodromies of certain families of square-tiled surfaces. arXiv:2206.06595 [math.DS]\n");
Print("  [DFH] A. Detinko, D. Flannery, A. Hulpke: Zariski Density and Computing in Arithmetic Groups. Math. Comp. 87 (2018), no. 310, 967–986.\n");
Print("  [GAPOrigami] S. Ertl, L. Junk, P. Kattler, A. Rogovskyy, P. Schumann, A. Thevis, G. Weitze-Schmithüsen:  GAP-package Origami. https://ag-weitze-schmithusen.github.io/Origami/\n");
Print("  [GAPArithmetic] A. Hulpke:  GAP-package Arithmetic. https://github.com/hulpke/arithmetic\n");

###################################
## Definition of the functions
###################################

#This function computes the Gram matrix of a basis B with respect to a bilinear form
#beta
#Input: A basis B as list of vectors and a bilinear form beta as GAP function, that takes
#two elements of the vector space, spanned by B, and returns a number.
#Output: A matrix
GramMatrix_For_KZM:= function(B, beta )
	local k,l, res, n;
	n := Length( B );
	res := [];
	for k in [1..n] do
		Add(res, []);
		for l in [1..n] do
			res[k][l] := beta(B[l], B[k]);
		od;
	od;
	return res;
end;


#This function computes the integral base change from a basis H of a module 〈H〉 ⊆ Zn of
#dimension 4 into a symplectic basis with respect to the symplectic form IntForm.
#Input: Basis H as a List of vectors vi ∈ Zn, a symplectic form IntForm which should be
#a function,that takes two vectors v, w ∈ Zn and returns an integer.
#Output: The base change as matrix A ∈ GL4(Z)
SymplBaseChange := function( H, IntForm)
	local M, res, N, G;
	M := [];
	res := [];
	G := GramMatrix_For_KZM( H, IntForm);
	Add(M, G[1]);
	Add(M, G[4]);
	res[1] := [1,0,0,0];
	res[3] := [0,0,0,1];
	N := NullspaceIntMat( TransposedMat( M ) );
	res[2] := N[1];
	res[4] := N[2];
	return TransposedMat( res );
end;

#This function computes a symplectic basis of the homology of an origami of genus 3 with
#respect to the intersection form.
#Input: An Origami O of genus 3 (from the Origami Package), a basis of the homology
#of O, the intersection form of the Origami as a GAP function, that takes two integral
#vectors and returns an integer. Output: A symplectic basis of the homology as a List of
#integral vectors.
SymplecticBasis := function( O, H, IntForm)
	local  T, B, c, i, j, NT ;
	B := [];
	NT := NonTautPartOfHomologyOrigami( O, H );
	T := SymplBaseChange(  NT, IntForm);
	for j in [1..4] do
		c := 0 * NT[1];
		for i in [1..4] do
			c := c + T[i][j]* NT[i];
		od;
		Add( B, c);
	od;
	return B;
end;

#This function computes a subgroup of the Kontsevich-Zorich Monodromy of an Origami
#in the family F7, which is conjugated to a subgroup of the standard symplectic group.
#Then it returns this conjugated subgroup.
#Input: An Origami O (from the Origami Package) from the family F7, a basis of the
#homology of O, the intersection form of the Origami as a GAP function, that takes two
#integral vectors and returns an integer. 
#Output: A list of matrices, generating the subgroup.
ConjugatedKontZorM := function( O, H, IntForm)
	local T, mult, L, L2,L3,K ,M, NT, CAction, ComputeMult, BaseChangeLatice, Stab, ind;	
	NT := NonTautPartOfHomologyOrigami( O, H );
    # Action of 
	CAction := function( n )
		local Actioni;
		Actioni := function(x , A )
			return (x *A) mod n;
		end;
		return Actioni;
	end;
    # Computes multiplicites for the lattice lambda ....
	ComputeMult := function(O, H, IntForm)
		local G, m, NT;
		NT := NonTautPartOfHomologyOrigami( O, H );		
		G := GramMatrix_For_KZM( SymplecticBasis( O, H, IntForm) , IntForm);
		m := Lcm( G[1][3], G[2][4]);
		return [m/G[1][3], m/G[2][4]];
	end;
    # Computes transformation matrix Ttilde:
	BaseChangeLatice := function( O, H, IntForm)
		local res;
		res := IdentityMat(4);
		res[1][1] := ComputeMult(O, H, IntForm)[1];
		res[2][2] := ComputeMult(O, H, IntForm)[2];
		return res;
	end;
# Computes transformation matrix T (cf. Section 6.2 in [BKKMNSVW]) which conjugates the stabiliser into the symplectic group 
	T := SymplBaseChange( NT, IntForm);
# L = List of generators of the Kontsevich-Zorich monodromy
	K := List( MatrixGeneratorsOfGroup( VeechGroup( O)), x-> ActionOfMatrixOnNonTaut(O, x, H) );
# Conjugate with T (= base change with T)
	L := List( K , x-> T^-1 * x * T);
# Compute stabilizer of lattice and the index
    mult :=  ComputeMult(O, H, IntForm);
	Stab := OrbitStabilizer( Group( L ), [1,0,0,0],  CAction(mult[1]));
	L2 := GeneratorsOfGroup( Stab.stabilizer );
	ind := Length( Stab.orbit );
# M = Ttilde:
	M := BaseChangeLatice( O, H, IntForm);
# Conjugate generators now with M = Ttilde: 
	L3 := List(L2, x-> M^ -1*x*M);
	return rec( KZM := K, T := T, mult := mult , GensOfStab := L2, KZMSG := L3, index := ind,  Ttilde := M );
end;


#This function computes a basis of the homology for origamis in the family F7, given by
#horizontal and vertical core cylinders.
#Input: Integers l and k for the number of squares in horizontal and vertical direction.
#Output: A basis of the homology as list of integer vectors.
HomologyForF7:= function( k, l)
	local res, i, c, L, n;
	n := k + l;
	L := Basis( Rationals^ ( 2*n ) );
	res := [];
	c := L[1];
	for i in [2..l] do
		c := c + L[i];
	od;
	Add(res, c);
	Add( res , L[l + 1] + L[l + 2]);
	Add(res, L[l + 3]);
	c := L[n + 1] + L[n + l + 1];
	for i in [1..(k-2)] do
		c := c+ L[ n + l + 2 + i];
	od;
	Add(res, c);
	Add(res, L[n + 2] + L[n + l + 2]);
	Add(res, L[n+3]);
	return res;
end;


#This function computes the intersection form for origamis in the family F7. Note that
#the intersection form works just for homology vectors, that are represented by linear
#combinations of core cylinders of horizontal and vertical cylinders.
#Input: elements v and w of the homology, given as integer vectors.
#Output: The number of intersections of v and w.
IntersectionFormForF7:= function( v, w )
	local res, i, n;
	res := 0;
	n := Length(v)/2;
	for i in [1..n] do
		res := res + ( v[i]* w[i + n]);
	od;
	for i in [(n+1)..(2*n)] do
res := res - ( v[i]* w[i - n]);
	od;
	return res;
end;

# This function calculates the index of an integral 2x2 matrix group, generated by gens in SL_(Z)
#Input: A list of matrices, generating a finite index subgroup of SL_2(Z)
#Output: The index
IndexOfSL2 := function( gens )
    local L, F2, S, T, K, x, CT;
    L := List( gens, x-> String( STDecomposition(x) ) );
    F2 := FreeGroup("S", "T");
    S := F2.S;
    T := F2.T;
    K := [];
    for x in L do
        if x <> "<identity ...>" then Add(K, ParseRelators([S,T], x)[1]); fi;
    od;
    CT := CosetTableFromGensAndRels( [S, T], [S^4, (S^3*T)^3, S^2*T*S^-2*T^-1], K : silent := true, max:= 1000);
    if CT = fail then return fail;
    else
     return Length( CosetTableFromGensAndRels( [S, T], [S^4, (S^3*T)^3, S^2*T*S^-2*T^-1], K )[1] ) ;
    fi;
end;

# This function calculates the index of an integral 2x2 matrix group, generated by gens in SL_(Z)
#Input: A list of matrices, generating a finite index subgroup of SL_2(Z)
#Output: The index
IndexOfSL2 := function( gens )
    local L, F2, S, T, K, x, CT;
    L := List( gens, x-> String( STDecomposition(x) ) );
    F2 := FreeGroup("S", "T");
    S := F2.S;
    T := F2.T;
    K := [];
    for x in L do
        if x <> "<identity ...>" then Add(K, ParseRelators([S,T], x)[1]); fi;
    od;
    CT := CosetTableFromGensAndRels( [S, T], [S^4, (S^3*T)^3, S^2*T*S^-2*T^-1], K : silent := true, max:= 1000);
    if CT = fail then return fail;
    else
     return Length( CosetTableFromGensAndRels( [S, T], [S^4, (S^3*T)^3, S^2*T*S^-2*T^-1], K )[1] ) ;
    fi;
end;


# This function computes the dimension of the sub-algebra of SL_(2g-2)(Q) generated by the Kontsevich-Zorich monodromy of an origami O
# Input: An origami O
# Output: the dimension d of the sub-algebra of SL_(2g-2)(Q) generated by the Kontsevich-Zorich monodromy of O
DimensionKoZoMondoromy := function( O ) 
	local A;
	A :=	Algebra( Rationals, List( MatrixGeneratorsOfGroup(VeechGroup(O)), x-> ActionOfMatrixOnNonTaut(O, x  ) ) );
	return Dimension( A ); #= (Genus(O)*2-2)^2;
end;


       

# The following function presents the actions of the 6 Dehn-twists from section 5.1 of the article [BKKMNSVW] as matrices M_. The matrices depend on N, M and m for the square-
# tiled surface O_{N,M} (M = 4+2*m, N > 0) and are given with respect to the basis B^(0) = {Sigma_i,Z_i} of the nontatutological part of the homology.
# M_v_KZM gives action of the Dehn-twist in direction (0,1)
# M_h_KZM gives action of the Dehn-twist in direction (1,0)
# M_delta_KZM gives action of the Dehn-twist in direction (1,1)
# M_chi_KZM gives action of the Dehn-twist in direction (1,-1)
# M_gamma_KZM gives action of the Dehn-twist in direction (1,2)
# M_alpha_KZM gives action of the Dehn-twist in direction (1,-2)
#
# Output: A record with the matrices, where the entries are polynomials in N, M and m
M_KZM := function()
	local P, N, M, m,  M_v_KZM, M_h_KZM, M_alpha_KZM, M_delta_KZM, M_chi_KZM, M_gamma_KZM;
	P :=PolynomialRing( Integers, ["N", "M", "m"] ); 
	N := IndeterminatesOfPolynomialRing(P)[1];
	M := IndeterminatesOfPolynomialRing(P)[2];	
	m := IndeterminatesOfPolynomialRing(P)[3];		
	M_v_KZM :=  [ [1, 0, 0, 0, 0, 0 ], [0, 1, 0, 0, 0, 0 ],[0, 0, 1, 0, 0, 0 ],[0, 3*M, 3*M, 1, 0, 0 ],[2*M, 2*M, 2*M, 0, 1, 0 ], [ -6, -12, -6*(N-1), 0, 0, 1]];
	M_h_KZM := [[1, 0, 0, 0, -3*N, -3*N], [0, 1, 0, -2*N, -2*N, -2*N ],  [0, 0, 1, 6, 12, 6*(M-1)], [0, 0, 0, 1, 0, 0 ], [ 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 1 ] ];
	M_delta_KZM := [[-2, -3, -3, 3, 3, 3 ],  [N+M-1, N+M, N+M-1, -N-M+1, -N-M+1, -N-M+1 ], [-3, -3, -2, 3, 3, 3 ], [-3, -3, -3, 4, 3, 3 ],  
	[N+M-1, N+M-1, N+M-1, -N-M+1, -N-M+2, -N-M+1 ], [-3, -3, -3, 3, 3, 4 ] ];

	M_chi_KZM := [[-M-N+4, -2*M-2*N+6, -2*M-2*N+6, -M-N+3, -2*M-2*N+6, -2*M-2*N+6],[-M-N+3,-2*M-2*N+7, -2*M-2*N+6, -M-N+3, -2*M-2*N+6, -2*M-2*N+6],[5,10,11,5,10,10],
      [M+N-3, 2*M+2*N-6, 2*M+2*N-6, M+N-2, 2*M+2*N-6, 2*M+2*N-6],[M+N-3, 2*M+2*N-6, 2*M+2*N-6, M+N-3, 2*M+2*N-5, 2*M+2*N-6],[-5,-10,-10,-5,-10,-9]];
	
	M_gamma_KZM := [[-M-2*N-3, -2*M-4*N-8, -(N-1)*(M+2*N+4), 0, -M-2*N-4,-(m+1)*(M+2*N+4)],[ M, 2*M+1, (N-1)*M, 0, M, (m+1)*M],[ M, 2*M, (N-1)*M+1,0, M, (m+1)*M],
      [ 2*M, 4*M, 2*(N-1)*M, 1, 2*M, 2*(m+1)*M],[2*M, 4*M, 2*(N-1)*M, 0, 2*M+1, 2*(m+1)*M],[-2*N-4, -4*N-8,-(N-1)*(2*N+4), 0,-2*N-4, -(m+1)*(2*N+4)+1]];
    
    M_alpha_KZM := [[-N-m+1,-N-m, (N-4)*(N+m),-N-m,-2*(N+m),-(3+m)*(N+m)],[-N-m,-N-m+1, (N-4)*(N+m), -N-m,-2*(N+m),-(3+m)*(N+m)],[m+6, m+6,-(N-4)*(m+6)+1, m+6,   
    2*(m+6), (3+m)*(m+6)],
      [N-6, N-6,-(N-4)*(N-6), N-5, 2*(N-6), (3+m)*(N-6)],[ 2*(N+m), 2*(N+m), -2*(N-4)*(N+m), 2*(N+m), 4*(N+m)+1, 2*(3+m)*(N+m)],
      [N-6, N-6,-(N-4)*(N-6), N-6, 2*(N-6), (3+m)*(N-6)+1]]; 
	return rec( M_v_KZM := M_v_KZM, M_h_KZM := M_h_KZM, M_alpha_KZM :=  M_alpha_KZM,  M_delta_KZM := M_delta_KZM, M_chi_KZM := M_chi_KZM, M_gamma_KZM := M_gamma_KZM);
end;


# The following function tests, weather the Kontsevich-Zorich monodromy of the  square-tiled surface O_N_M  (M =4+2*m) is Zariski dense. O_N_M was defined in  section 5.1 of the article  [BKKMNSVW]. This result is used in section 5.2.
#Input: the integers m and N such that M = 4+2m
#Output: True if the KZM is dense, false if not.
IsDense_O_N_M_KZM := function( m, N)
    local M, J,B,J1, M1, M2, M3, M4, M5, M6, B1, B2, B3, B4, B5, B6, t, t2, t3, t4, t5, t6, K, Matrices, A;
	
	M:=4+2*m;

	# intersection form with repect to the basis B^(0) = \{\Sigma_i,Z_i\} f the nontatutological part of the homology of O_{N,M}. 
	J:=[[0,0,0,0,1,-1],[0,0,0,1,1,-2],[0,0,0,-1,-2,-N-M+1],[0,-1,1,0,0,0],[-1,-1,2,0,0,0],[1,2,N+M-1,0,0,0]];

	#change of basis for nice intersection form
	B:=[[N+M+2,-2*(N+M+2),0,0,0,1],[0,0,0,0,0,1],[0,-(N+M+2),0,0,0,1],[0,0,-1-N-M,0,1,0],[0,0,1,1,0,0],[0,0,1,0,0,0]];;

	J1:=[[0,0,0,1,0,0],[0,0,0,0,1,0],[0,0,0,0,0,1],[-1,0,0,0,0,0],[0,-1,0,0,0,0],[0,0,-1,0,0,0]];;
      
   
	# M1,.., M6 are the actions of the Dehn-twists in the following directions on H^(0)_1(O, Q) 

	# dicrection (1,1)
	M1:=[[-2, -3, -3, 3, 3, 3 ],  [N+M-1, N+M, N+M-1, -N-M+1, -N-M+1, -N-M+1 ], [-3, -3, -2, 3, 3, 3 ], [-3, -3, -3, 4, 3, 3 ],  
	[N+M-1, N+M-1, N+M-1, -N-M+1, -N-M+2, -N-M+1 ], [-3, -3, -3, 3, 3, 4 ] ];;
      

	# dicrection (1,-1)
	M2:=[[-M-N+4, -2*M-2*N+6, -2*M-2*N+6, -M-N+3, -2*M-2*N+6, -2*M-2*N+6],[-M-N+3,-2*M-2*N+7, -2*M-2*N+6, -M-N+3, -2*M-2*N+6, -2*M-2*N+6],[5,10,11,5,10,10],
	[M+N-3, 2*M+2*N-6, 2*M+2*N-6, M+N-2, 2*M+2*N-6, 2*M+2*N-6],[M+N-3, 2*M+2*N-6, 2*M+2*N-6, M+N-3, 2*M+2*N-5, 2*M+2*N-6],[-5,-10,-10,-5,-10,-9]];;
     

	# dicrection (1,2)
	M3:=[[-M-2*N-3, -2*M-4*N-8, -(N-1)*(M+2*N+4), 0, -M-2*N-4,-(m+1)*(M+2*N+4)],[ M, 2*M+1, (N-1)*M, 0, M, (m+1)*M],[ M, 2*M, (N-1)*M+1,0, M, (m+1)*M],
	[ 2*M, 4*M, 2*(N-1)*M, 1, 2*M, 2*(m+1)*M],[2*M, 4*M, 2*(N-1)*M, 0, 2*M+1, 2*(m+1)*M],[-2*N-4, -4*N-8,-(N-1)*(2*N+4), 0,-2*N-4, -(m+1)*(2*N+4)+1]];;
      

	# dicrection (1,-2)
	M4:=[[-N-m+1,-N-m, (N-4)*(N+m),-N-m,-2*(N+m),-(3+m)*(N+m)],[-N-m,-N-m+1, (N-4)*(N+m), -N-m,-2*(N+m),-(3+m)*(N+m)],[m+6, m+6,-(N-4)*(m+6)+1, m+6, 2*(m+6), (3+m)*(m+6)],
	[N-6, N-6,-(N-4)*(N-6), N-5, 2*(N-6), (3+m)*(N-6)],[ 2*(N+m), 2*(N+m), -2*(N-4)*(N+m), 2*(N+m), 4*(N+m)+1, 2*(3+m)*(N+m)],
	[N-6, N-6,-(N-4)*(N-6), N-6, 2*(N-6), (3+m)*(N-6)+1]];;
      

	# dicrection (1,0)
	M5:=[[1, 0, 0, 0, -3*N, -3*N], [0, 1, 0, -2*N, -2*N, -2*N ],  [0, 0, 1, 6, 12, 6*(M-1)], [0, 0, 0, 1, 0, 0 ], [ 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 1 ] ];;
      

	# dicrection (0,1)
	M6:=[ [1, 0, 0, 0, 0, 0 ], [0, 1, 0, 0, 0, 0 ],[0, 0, 1, 0, 0, 0 ],[0, 3*M, 3*M, 1, 0, 0 ],[2*M, 2*M, 2*M, 0, 1, 0 ], [ -6, -12, -6*(N-1), 0, 0, 1]];;
      

	# Change of basis into the lattice
	B1:=Inverse(B)*M1*B;
 	B2:=Inverse(B)*M2*B;
	B3:=Inverse(B)*M3*B;
	B4:=Inverse(B)*M4*B;
	B5:=Inverse(B)*M5*B;
	B6:=Inverse(B)*M6*B;



	# taking powers and conjugating in order to get into the normal closure of the transvection.
	t:=B1;;
	t2:=Inverse(B2)*t*(B2);
	t3:=Inverse(B3)*t*(B3);
	t4:=Inverse(B4)*t*(B4);
	t5:=Inverse(B5^(N+M+2))*t*(B5^(N+M+2));
	t6:=Inverse(B6)*t*(B6);


	K := Rationals;
	Matrices := [t,t2,t3,t4,t5,t6] * One(K);
	A:=Algebra(K, Matrices);
	if Dimension(A) = 36 then
		return true; #Print("m=", m, ",N=",N, ",M=",M, ": Full\n");
	else
		return false; #Print("m=", m, ",N=",N, ",M=",M,   ": Not full\n");
	fi;
end;



#################################################################################
######### Example functions presenting the computations from the article  ########
#################################################################################



#	return rec( KZM := K, KZMSG := L, index := ind, T := T, Ttilde := M ); (Kann das weg oder ist das Kunst? :))
# Example from Section 6.2 in [BKKMNSVW]:
Example1_AKZ := function()
	local O_3_5, H, Htilde,  VG, Gens, Transvec, P, r, R,Utilde;
	Print("\n\nHere we compute the results from Section 6.2 in  [BKKMNSVW]:");
    Print("\n\nWe consider the Origami O_3_5 = ");
	O_3_5 := Origami((1, 2, 3, 4, 5)(6, 7), (1, 6, 8)(2, 7));
	Print(O_3_5);
	Print("\n\nComputation of its Veech group VG:");
    VG := VeechGroup(O_3_5);
    Print("\nIndex in SL(2,Z):"); Print(Index(VG));
    Gens := Set(GeneratorsOfGroup(VG));;
    Print("\nNumber of generators:");Print(Length(Gens));
	Print("\n\nThe fundamental matrix G of the restriction of the intersection form to the non-taut part:\n");
    Display(GramMatrix_For_KZM( NonTautPartOfHomologyOrigami(O_3_5, HomologyForF7(3 , 5)),IntersectionFormForF7));
    Print("\n\nThe relevant data of the Kontsevich-Zorich monodromy of O_3_5 are computed by the function 'ConjugatedKontZorM':"); 
    R := ConjugatedKontZorM( O_3_5, HomologyForF7(3 , 5), IntersectionFormForF7 );
    Print("\n\nIts first output 'KZM' is a set of generators of the  Kontsevich-Zorich monodromy. 18  of the 102 generators are eliminated as doubles: ");
	H := R.KZM; Print("H = ");ViewObj( Group(Set(H))  );
	#Print("\n\n We compute the Kontsevich-Zorich monodromy of O_3_5\n H = "); 
	# R := ConjugatedKontZorM( O_3_5, HomologyForF7(3 , 5), IntersectionFormForF7 );
	# H := R.KZM; ViewObj( Group( Set( H ) ) );
    Print("\n\n Its output 'T' is a transformation matrix which brings G into the normal form G' from 6.2 in [BKKMNSVW]: T = \n");
    Display( R.T );
    Print("\n Its  output 'mult' contains the numbers with which we have to multiply the two first vectors in the base B' in order to obtain the new base C that generates the desired sublattice Lambda:\n");
    Display(R.mult);
	#Print("\n Then we perform a change of basis with the transformation matrix T = \n");
    Print("\n Its  output 'GensOfStab' contains a list of generators of the stabilizer U' of Lambda in H' = T^{-1}HT.");
    Print("\n The index of U' in H' is: ");
    Print( R.index );
    Print("\n\n Its  output'KZMSG'  contains a list of generators of Utilde which is the conjugate of U' with the base change matrix Ttilde = \n");
	Display(R.Ttilde);
	Print("Utilde is the desired subgroup of SP(4,Z): Utilde =\n");
	Utilde := Group(R.KZMSG);
	ViewObj(Utilde);
    Print("\nWe use the following transvection in the function PrimesForDense from [GAPArithmetic] in order to compute the index and the congruence level:\n");
    Transvec := Filtered(R.KZMSG,IsTransvection)[1]; Print("Trv =\n"); Display(Transvec);
    Print("Computation of LEVEL and INDEX with 'PrimesForDense' and 'MaxPCSPrimes' from [GAPArithmetic]:\n");
	P := PrimesForDense( Utilde , Transvec, 2);
	r:=  MaxPCSPrimes(  Utilde , P, 2 );
	Print("\nResult:");
	Print("\nLevel of Utilde: " ); Print(r[1]);	
	Print("\nIndex of  Utilde in SP_4(Z): "); Print(r[2]);
return();
end;


# Computations for Theorem 25 in [BKKMNSVW]:
# We compute the table with the indices of the Kontssevich-Zorich monodromy for the L-Origamis from section 6.1
# Run  'Example2_AKZ(20);' to get the result from Theorem 25.

Example2_AKZ := function(n)
	local LOrigami;
    # The folllwing function returns the list of all L-shape origamis with leg size <= n and <= m.
	LOrigami := function( n,m)
		local l, hlist, vlist;
		hlist := [2..n];
		hlist[n] := 1;
		vlist := [n+1];
		Append(vlist, [2..n]);
		Append( vlist, [(n+2) .. (n + m - 1)]);
		vlist[ n + m - 1] := 1;
		return Origami( PermList( hlist ), PermList( vlist ) );
	end;
    # The function returns the index of the Kontsevich-Zorich-monodromy in SL(2,Z) for the origamis in the list LOrigami.
	Print("\n\n Here we compute the index of the Kontsevich-Zorich monodromy of L-origamis from section 6.1 in the article.");
	Print("\n We print a table, in which the entry (a,b) belongs to the L-origami L(a + 1,b + 1) = Origami( (1..a), (1 (a+1)..(a+b)) ). \n\n");
	Display( List( [2..n], x->List([2..n], y-> IndexOfSL2( GeneratorsOfGroup(  ShadowVeechGroup(LOrigami(x,y))) )) )  );
end;



# Computations of the Table with the indices of the Z-Origamis in Section 6.2 in [BKKMNSVW]:
# Run Example3_AKZ(20) to get the results from the table.
Example3_AKZ := function(n)
	local ZOrigami, i, j, res;
	 ZOrigami := function( a,b ) # ZOrigami 
		local vlist, hlist;
		hlist := [2..a];
		Add(hlist, 1);
		Append(hlist, [a+2..(a+b)]);
		Add(hlist, a+1);
		vlist :=[1..(a+b)];
	 	vlist[a] := a+1;
	 	vlist[a+1] := a;
	 	return Origami( PermList( hlist ), PermList( vlist ) );
	 end;
	 res := [];
	 for i in  [2..n] do 
	 	Add( res, []);
	 	for j in [2..n] do
	 		if i = j then res[i - 1][j - 1] := "-";
	 		else 
	 			res[ i- 1][j - 1] := IndexOfSL2( GeneratorsOfGroup(  ShadowVeechGroup( ZOrigami(i,j) ) ) );
	 		fi;
	 	od;
	 od;	
	Print("\n\n This function computes the index of the Kontsevich-Zorich monodromy of Z-origamis from section 6.2 in the article.");
	Print("\n We print a table, in which the entry (k-1,l-1) belongs to the Z-origami O(k,l) = Origami( (1..k) ((k+1).. k+l), (k (k+1)) ). \n\n");
    Display( res);
end;

# This function computes the dimension of the sub-algebra of SL_(2g-2)(Q) generated by the Kontsevich-Zorich monodromy of an origami O
# Input: An origami O
# Output: the dimension d of the sub-algebra of SL_(2g-2)(Q) generated by the Kontsevich-Zorich monodromy of O
DimensionKoZoMondoromy := function( O ) 
	local A;
	A :=	Algebra( Rationals, List( MatrixGeneratorsOfGroup(VeechGroup(O)), x-> ActionOfMatrixOnNonTaut(O, x  ) ) );
	return Dimension( A ); #= (Genus(O)*2-2)^2;
end;

# We apply DimensionKoZoMondoromy to the origami  Origami ((2, 3, 4)(5, 7, 6), (1, 2, 3, 5, 4, 6, 7)) from section 6.3  in [BKKMNSVW]
Example4_KZM := function()
	local O,G,L, A1, A2, B, Btilde;
	Print("\n This function computes the dimension of the Kontsevich-Zorich monodromy of the origami O = Origami( (2, 3, 4)(5, 7, 6), (1, 2, 3, 5, 4, 6, 7) ) from section 6.3 in [BKKMNSVW]:\n");
	O := Origami( (2, 3, 4)(5, 7, 6), (1, 2, 3, 5, 4, 6, 7) );
    G := VeechGroup(O);
    Print("\nIndex of the Veech group:" ); Print(Index(G)); Print("\n");
    L := MatrixGeneratorsOfGroup(G); A1 := L[3]; A2 := L[1];
    Print("Generators of the Veech group:"); Print(L);Print("\n");
    Print("\nComputations for the Schreier coset graph:\n");
    Print("The action of T on the cosets:"); Print(TAction(G)); Print("\n");
    Print("The action of S on the cosets:"); Print(SAction(G)); Print("\n");
    ActionOfMatrixOnNonTaut(O, A1); 


	B := [ [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
	[ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
	[ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ], 
	[ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ] ];
	Btilde := [ [ 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0 ], 
	[ 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0 ], 
	[ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0 ] ];


	Print("\nWe finally compute the matrices from section 6.3:");
	Print("\nD1 =\n");
	Display( ActionOfMatrixOnHom(O, A1, B ) );
	Print("D2 =\n");
	Display( ActionOfMatrixOnHom(O, A2, B ) );	
	Print("E1 =\n");
	Display( ActionOfMatrixOnHom(O, A1, Btilde) );
	Print("E2 =\n");	
	Display( ActionOfMatrixOnHom(O, A2, Btilde) );
	Print("\nDimension of the Kontsevich-Zorich monodromy: ");Print( DimensionKoZoMondoromy( O ) );

end;


# We check (cf. Section 5.2 in [BKKMNSVW]) for the origamis O_{N,M}  that the algebra generated by  the Kontsevich-Zorich monodromy has full dimension for N in {4,5,...,50} and M = 2m+4 with m in {0,1,2,...,50}.
Example5_KZM := function()
	local N,m,M;
	Print("\nThis function checks whether the algebra generated by the Kontsevich-Zorich monodromy of the origami O_{N,M} has full dimension for N in {4,5,...,50} and M = 2m+4 with m in {0,1,2,...,50}.\n");
    for N in [4..50] do
        for m in [0..50] do
            M := 2*m+4;
            Print("\n(N,M) = ("); Print(N);Print(",");Print(M);Print("):");Print(IsDense_O_N_M_KZM(m,N));
        od;
    od;
end;


# The following function returns the matrix M_delta_KZM (from Section 5.1 in [BKKMNSVW]) which gives the  action of the Dehn-twist in direction (1,1)  with respect to the basis B^(0) = {Sigma_i,Z_i} of the nontatutological part of the homology. The matrix depends on N, M and m for the square-tiled surface O_{N,M} (M = 4+2*m, N > 0).
BigMatrix1 := function()
    Print("\nM_delta^(0) = \n");
    return(M_KZM().M_delta_KZM);   
end;

# The following function returns the matrix M_chi_KZM (from Section 5.1 in [BKKMNSVW]) which gives the  action of the Dehn-twist in direction (1,-1)  with respect to the basis B^(0) = {Sigma_i,Z_i} of the nontatutological part of the homology. The matrix depends on N, M and m for the square-tiled surface O_{N,M} (M = 4+2*m, N > 0).
BigMatrix2 := function()
     Print("\nM_chi^(0) = \n");    
    return(M_KZM().M_chi_KZM);   
end;

# The following function returns the matrix M_alpha_KZM (from Section 5.1 in [BKKMNSVW]) which gives the  action of the Dehn-twist in direction (1,-2)  with respect to the basis B^(0) = {Sigma_i,Z_i} of the nontatutological part of the homology. The matrix depends on N, M and m for the square-tiled surface O_{N,M} (M = 4+2*m, N > 0).
BigMatrix3 := function()
    Print("\nM_alpha^(0) = \n");     
    return(M_KZM(). M_alpha_KZM);   
end;

# The following function returns the matrix M_gamma_KZM (from Section 5.1 in [BKKMNSVW]) which gives the  action of the Dehn-twist in direction (1,2)  with respect to the basis B^(0) = {Sigma_i,Z_i} of the nontatutological part of the homology. The matrix depends on N, M and m for the square-tiled surface O_{N,M} (M = 4+2*m, N > 0).
BigMatrix4 := function()
    Print("\nM_gamma^(0) = \n");   
    return(M_KZM().M_gamma_KZM);   
end;
