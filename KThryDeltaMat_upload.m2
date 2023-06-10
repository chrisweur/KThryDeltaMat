-*------------------------------------------------------------------------------------------
Macaulay2 code accompanying "K-classes of delta-matroids and equivariant localization"

Author: Christopher Eur
Comments: Intersecting feasible sets in [n, bar n] with [n],
           delta-matroids are lists of subsets of [n] for this code.
------------------------------------------------------------------------------------------*-


--------< computations on the OGr(n;2n+1) as a GKM variety >-------------

needsPackage "GKMVarieties"

--internal auxiliary function: 
--input: a Laurent polynomial f and a GKMVariety X
--output: a Laurent polynomial f considered as an element of X.characterRing
toCharacterRing = (X,f) -> (
    if f == 1 then return 1_(X.characterRing);
    R := ring f; n := #(gens R);
    if not #(gens X.characterRing) == n then
        error "rings have different number of variables";
    sub(f,apply(n, i -> R_i=>X.characterRing_i))    
)


--input: a matrix M whose columns are vertices of P(D) and GKMVariety X = OGr(n;2n+1).
--output: the T-eqv K-class of O_{T\cdot L} if D had a realization L.
combOTL = method()
combOTL(GKMVariety,Matrix) := KClass => (X,M) -> (
    M = sub(M,ZZ);
    R := X.characterRing;
    --Xdenoms := hashTable apply(X.points, p -> (p, product((X.charts)#p, l -> 1-R_l)));
    n := #(elements first first X.points);
    E := set toList(0..(n-1));
    b := numcols M;
    Mcols := apply(b, i -> sub(matrix M_i,ZZ));
    L := apply(X.points, s -> (
	    f := (first s) * E;
	    C := matrix apply(n, i -> if member(i,f) then {1} else {0});
	    if not member(C,Mcols) then return 0_R;
	    p := position(Mcols, i -> i == C);
	    Mp := (M - matrix toList(b : M_p));
	    Mp = Mp_(delete(p,toList(0..(b-1))));
	    HS := hilbertSeries affineToricRing Mp;
	    numer := toCharacterRing(X,value numerator HS);
	    denom := toCharacterRing(X,value denominator HS);
	    Xdenom := product((X.charts)#s, l -> 1 - R_l);
	    x := symbol x;
    	    S := QQ[x_0..x_(#(gens R)-1)];
	    (ratio, goBack) = toSequence toFraction(numer * Xdenom, denom, S);
	    goBack ratio
	    )
	);
    makeKClass(X,L)    
    )

--input: an integer n
--output: X = generalizedFlagVariety("B",n,{n,n}), O1 = a square-root of ampleKClass X,
--Qdual = the KClass of the dual of the tautological quotient bundle,
--wedgesQdual = the list of exterior powers of Qdual
initializeBundles = n -> (
    X := generalizedFlagVariety("B",n,{n,n});
    R := X.characterRing;
    E := set toList(0..(n-1));
    KLO1 := apply(X.points, p -> product(elements ((first p)*E), i -> R_i));
    O1 := makeKClass(X,KLO1);
    KLQdual := apply(X.points, p -> 1+ sum apply(elements E,i -> (
		if not member(i,first p) then R_i
		else R_i^(-1)
		)
	    )
	);
    Qdual:= makeKClass(X,KLQdual);
    wedgesQdual := {trivialKClass X} | apply(n+1, i -> (
	    KL := apply(X.points, p -> sum((subsets(terms Qdual.KPolynomials#p,i+1))/product));
	    makeKClass(X,KL)
	    )
    	);
    (X,O1,Qdual,wedgesQdual)
    )



--optimized for OGr comp for now
fastEuler = method();
fastEuler(KClass) := QQ => C -> (
    X := C.variety;
    R := X.characterRing;
    Xdenoms := hashTable apply(X.points, p -> (p, product((X.charts)#p, l -> phi(1-R_l))));
    q := symbol q;
    S := frac(QQ[q]);
    phi := map(S,R,apply(numgens R, i -> R_i => q^(i+1)));
    sub(sum(keys Xdenoms, k -> (phi C.KPolynomials#k) / Xdenoms#k), S_0 => 1)
    )


--optimized fast push-pull Atiyah-Bott with single variable substitution trick
--input: delta-matroid D as a list of subsets of [n], and the integer n
--output: list of the coefficients of the R-polynomials, in the ascending degree order
fastPushPull = method(Options => {Timed => false});
fastPushPull(List,ZZ) := List => opts -> (D,n) -> (
    (X,O1,Qdual,wedgesQdual) := initializeBundles n;
    E := set toList(0..(n-1));
    R := X.characterRing;
    q := symbol q;
    S := frac(QQ[q]);
    M := basisIndicatorMatrix(D,n);
    b := numcols M;
    Mcols := apply(b, i -> sub(matrix M_i,ZZ));
    McolDiffs := apply(subsets(Mcols,2), i -> flatten entries (first i - last i));
    wList := sort(subsets(3*n,n), l -> sum l);
    weightFound := false;
    wCounter := -1;
    while not weightFound do (
	wCounter = wCounter + 1;
	w := wList_wCounter/(i -> i+1);
	if all(McolDiffs, l -> sum(n, i -> w_i * l_i) != 0) then weightFound = true;
	);
    w = wList_wCounter/(i -> i+1);
    phi := map(S,R,apply(numgens R, i -> R_i => S_0^(w_i)));
    if opts.Timed then OTL := time hashTable apply(b, i -> (
	    s := set positions(flatten entries Mcols_i, j -> j != 0);
	    Mi := (M - matrix toList(b : M_i));
	    Mi = Mi_(delete(i,toList(0..(b-1))));
	    HS := hilbertSeries affineToricRing Mi;
	    numer := (toList factor numerator HS)/(i -> toCharacterRing(X,value i));
	    numer = product (numer/phi);
	    denom := (toList denominator HS)/(i -> toCharacterRing(X,value i));
	    denom = product (denom/phi);
	    (s, {numer, denom})
	    )
	)
    else OTL = hashTable apply(b, i -> (
	    s := set positions(flatten entries Mcols_i, j -> j != 0);
	    Mi := (M - matrix toList(b : M_i));
	    Mi = Mi_(delete(i,toList(0..(b-1))));
	    HS := hilbertSeries affineToricRing Mi;
	    numer := (toList factor numerator HS)/(i -> toCharacterRing(X,value i));
	    numer = product (numer/phi);
	    denom := (toList denominator HS)/(i -> toCharacterRing(X,value i));
	    denom = product (denom/phi);
	    (s, {numer, denom})
	    )
	);
    WQq := wedgesQdual/(c -> c.KPolynomials)/(h -> applyValues(h, i -> phi i));
    WQq = WQq/(h -> applyKeys(h, i -> (E * (first i))));
    O1q := applyValues(O1.KPolynomials, i -> phi i);
    O1q = applyKeys(O1q, i -> (E * (first i)));
    L := {};
    if opts.Timed then L = apply(n+2, d -> (
	    time sum(keys OTL, s -> (OTL#s)_0 / (OTL#s)_1 * O1q#s * (WQq_d)#s)
	    )
	)
    else L = apply(n+2, d -> sum(keys OTL, s -> (OTL#s)_0 / (OTL#s)_1 * O1q#s * (WQq_d)#s));
    L/(f -> sub(f, S_0 => 1))
    )


--just testing the last one (i.e. chi of OTL(-1))
lastCoeff = D -> (
    Maug := matrix{toList((#D:1))} || basisIndicatorMatrix(D,n);
    R := QQ[x_0..x_(#D-1)];
    I := toricGroebner(Maug,R);	   
    hp := hilbertPolynomial(I, Projective => false);
    sub(hp, (ring hp)_0 => -1)
    )

-------------------------< delta-matroids >-----------------------
needsPackage "Polyhedra"

--the indicator vector of a list s in ZZ^n
setIndicator(List,ZZ) := (s,n) -> apply(n, i -> if member(i,s) then 1 else 0)

--vertices of the polytope P(D)
basisIndicatorMatrix(List,ZZ) := Matrix => (D,n) -> transpose matrix apply(D,s -> setIndicator(s,n))

--the polytope P(D)
toPolytope = (D,n) -> convexHull basisIndicatorMatrix(D,n)
 
--the polytope hat(P(D)) = 2P(D) - (1,...,1)
toPolytope2 = (D,n) -> 2*toPolytope(D,n) + convexHull transpose matrix {toList(n:-1)}

--checking type B generalized permutohedron
checkBGP = method()

--check given a vector (in a form of a List) is a type B root
checkBGP(List) := L -> (
    nonzeros := select(L/abs, i -> i != 0);
    #nonzeros <= 2 and #(unique nonzeros) == 1 
    )

--check given a polytope P whether it is a type B generalized permutohedron
checkBGP(Polyhedron) := P -> (
    V := Polyhedra$vertices P;
    E := Polyhedra$faces(dim P - 1,P)/first/(i -> V_(first i) - V_(last i));
    all(E, e -> checkBGP flatten entries e)
    )

--input: list D of feasible subsets, and n, and polynomial ring S
--output: the interlace polynomial of D, with variable in S
interlacePolynomial = method()
interlacePolynomial(List,ZZ,Ring) := (D,n,S) -> (
    if n == 0 then return 1_S;
    if all(D, l -> member(n-1,l)) or all(D, l -> not member(n-1,l)) 
    then return (S_0 + 1) * interlacePolynomial(D/(l -> delete(n-1,l)),n-1,S);
    interlacePolynomial(select(D, l -> not member(n-1,l)),n-1,S) + 
    interlacePolynomial((select(D, l -> member(n-1,l)))/(l -> delete(n-1,l)),n-1,S)
    )

--given the basisIndicatorMatrix M of a delta-matroid,
--tests whether the base polytope is very ample in the lattice that the vertices generate.
testVeryAmple = M -> (
    b := numcols M;
    CL := apply(b, i -> (
	    Mi := (M - matrix toList(numcols M : M_i));
	    Mi = Mi_(delete(i,toList(0..(b-1))));
	    (D,P,Q) := smithNormalForm sub(Mi,ZZ);
	    (inverse Q)^(toList(0..(rank Mi - 1)))
	    )
    	);
    all(CL, l -> (
	    cols := set apply(numcols l, i -> matrix l_i);
	    H := set hilbertBasis coneFromVData l;
	    isSubset(H,cols)
	    )
    	)
    )


isEvenDelta = D -> #(unique apply(D, l -> #l % 2)) == 1

end
------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------
