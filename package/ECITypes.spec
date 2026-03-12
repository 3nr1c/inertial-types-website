declare verbose ECITypes, 1;

import "utils.m" : AllQuadraticExtensions, OptimalNorms, IsValidExceptionalExtension, ElementCoordinates;
import "sequences.m" : UComplex, ConComplex, BaseValues, ExtValues;
import "characters.m" : FastCharactersOfOrder, FastCharactersOfPrimePowerOrder;

///////// PRINCIPAL SERIES //////////
intrinsic PrincipalSeries(F : Order := 0, TrivialOn := [], QuadraticOn := [], MyComplex:=[* *]) 
    -> SeqEnum[PSInType]
{Compute all inertial types from principal series over F}
    if #MyComplex eq 3 then
        groups := MyComplex[1];
        maps := MyComplex[2];
        lift := MyComplex[3];
        f := #groups;
    else
        p, ram_deg, in_deg, pi, N := BaseValues(F);
        f := Floor(N/2);
        groups, maps, lift := UComplex(F, f);
    end if;
    proj := Inverse(lift);
    
    Orders := {2, 3, 4, 6};
    if Order in Orders then
        Orders := {Order};
    elif Order ne 0 then
        Orders := {}; // make sure the output will be empty
    end if;

    Elements := [];
    Values := [];

    for e in TrivialOn do
        Append(~Elements, proj(e));
        Append(~Values, 0);
    end for;

    for e in QuadraticOn do
        Append(~Elements, 2*proj(e));
        Append(~Values, 0);
    end for;

    PS := [];
    for n in Orders do
        PS cat:= [
            PrincipalSeriesType(phi) 
            : phi in FastCharactersOfOrder(groups[1], n, maps, lift : Elements:=Elements, Values:=Values)
        ];
    end for;

    return PS;
end intrinsic;


// intrinsic ExceptionalTypes(F)
// end intrinsic;

// intrinsic ExceptionalTypes(F, L)
//     assert IsValidExceptionalExtension(F, L);
// end intrinsic;

// intrinsic ExceptionalTypes(F, L, K)
//     assert IsValidExceptionalExtension(F, L);
//     // check that K generates a Galois submodule of dim 2
// end intrinsic;

////// SUPERCUSPIDAL UNRAMIFIED TYPES /////
function SupercuspidalUnramified(F, K, f : Order := 0, TrivialOn := [], QuadraticOn := [])
    if Valuation(Discriminant(K,F)) gt 0 then
        error Error("The extension K|F is not unramified");
    end if;

    groups, maps, lift := ConComplex(F, K, f);
    proj := Inverse(lift);

    Orders := {3, 4, 6};
    if Order in Orders then
        Orders := {Order};
    elif Order ne 0 then
        Orders := {}; // make sure the output will be empty
    end if;

    Elements := [];
    Values := [];

    for e in TrivialOn do
        Append(~Elements, proj(e));
        Append(~Values, 0);
    end for;

    for e in QuadraticOn do
        Append(~Elements, 2*proj(e));
        Append(~Values, 0);
    end for;

    SCU := [];
    for n in Orders do
        SCU cat:= [
            SupercuspidalUnramifiedType(phi, F)
            : phi in FastCharactersOfOrder(groups[1], n, maps, lift)
        ];
    end for;

    return SCU;
end function;

intrinsic SupercuspidalUnramified(F : Order := 0, TrivialOn := [], QuadraticOn := [])
    -> SeqEnum[SCUInType]
{TrivialOn and QuadraticOn are elements in UnramifiedExtension(F,2)}
    K := UnramifiedExtension(F, 2);

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    f := Floor(N/2);

    return SupercuspidalUnramified(F, K, f : Order := Order, TrivialOn := TrivialOn, QuadraticOn := QuadraticOn);
end intrinsic;

///// SUPERCUSPIDAL RAMIFIED ////
function SupercuspidalRamified2(F, K, f, c, VarepsGenerators : KernelElements := [])
    assert Prime(F) eq 2;

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    Cond, pi, Gal, y := ExtValues(F, K);
    groups, maps, lift := ConComplex(F, K, f);

    proj := Inverse(lift);
    bar_y2 := 2*proj(y);

    Elements := [proj(g) : g in VarepsGenerators | not IsIdentity(proj(g))];
    Values := [2 : g in VarepsGenerators | not IsIdentity(proj(g))];
    
    Append(~Elements, bar_y2);
    if (in_deg mod 2) eq 0 then
        // (in_deg mod 2) eq 0 checks if x^2+x+1 splits in F
        // Triply imprimitive with n = 4, characters must be quadratic on y
        Append(~Values, 0);
    else
        // Simply imprimitive with n = 4, characters must *not* be quadratic on y
        Append(~Values, 2);
    end if;

    for e in KernelElements do
        Append(~Elements, e);
        Append(~Values, 0);
    end for;

    return [
        SupercuspidalRamifiedType(phi, F)
        : phi in FastCharactersOfPrimePowerOrder(groups[1], 2, 2, maps, lift : Elements:=Elements, Values:=Values)
    ];
end function;

function SupercuspidalRamified3(F, K, f, c, VarepsGenerators)
    assert Prime(F) eq 3;

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    Cond, pi, Gal, y := ExtValues(F, K);
    groups, maps, lift := ConComplex(F, K, f);

    proj := Inverse(lift);
    VarepsGenerators := [proj(g) : g in VarepsGenerators | not IsIdentity(proj(g))];
    Values := [3 : g in VarepsGenerators];

    return [
        SupercuspidalRamifiedType(phi, F)
        : phi in FastCharactersOfOrder(groups[1], 6, maps, lift : Elements:=VarepsGenerators, Values:=Values)
    ];
end function;


function InternalSCR(F, K, f, c, VarepsGenerators)
    p := Prime(F);
    // print("p="),p;
    if p eq 2 then
        return SupercuspidalRamified2(F, K, f, c, VarepsGenerators);
    elif p eq 3 then
        return SupercuspidalRamified3(F, K, f, c, VarepsGenerators);
    else
        error Error("Prime must be 2 or 3");
    end if;
end function;

intrinsic SupercuspidalRamified(F::FldPad, K::FldPad) -> SeqEnum[SCRInType]
{Return SCRs over F induced by a specific quadratic field}
    assert Degree(K, F) eq 2;

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    K := K;
    Cond, pi, Gal, y := ExtValues(F,K);
    c := Cond;
    require Cond gt 0 : "Ramification degree must be >1";

    f := Max(N-Cond, 2*Cond);
    groups, maps, lift := UComplex(F, Floor(N/2));
    VarepsGenerators := {K!lift(g) : g in Generators(groups[1])};
    return InternalSCR(F, K, f, c, VarepsGenerators);
end intrinsic;

function SCRMatched(F, K, SCR)
// F::FldPad, K::SeqEnum[FldPad], SCR::SeqEnum[SCRInType]
    assert #K in [2, 3];

    // This list will contain the types
    TriplyImprimitiveTypes := [];

    // We set up the triple of fields
    y1 := Discriminant(K[1], F);
    y2 := Discriminant(K[2], F);

    if #K eq 3 then
        y3 := Discriminant(K[3], F);
    else
        Fx<x> := PolynomialRing(F);
        y3 := y1*y2;
        Append(~K, SplittingField(x^2 - y3));
    end if;

    // we compute the SCR types for each field
    while #SCR lt 3 do
        Append(~SCR, SupercuspidalRamified(F, K[#SCR + 1]));
    end while;

    R1<X> := PolynomialRing(K[1]);
    E1 := SplittingField(X^2 - y2);

    e2, e3 := Sqrt(E1!y2), Sqrt(E1!y3);
    s1, s2, s3 := Sqrt(K[1]!y1), Sqrt(K[2]!y2), Sqrt(K[3]!y3);

    // Compute generators of the group of norms from E1
    c := Max([tau`Character`CondExp: tau in SCR[1]]);
    Uf, UpStairsUf := OptimalNorms(E1,K[1],c);

    // For the generators of the group in E1, we need their expressions 
    // in a K[1]- (resp. K[2]-, K[3])-basis of E1, to compute the norm down to each subfield
    UnitCoordsK2Basis := [ElementCoordinates(g,[1,e2]): g in UpStairsUf];
    UnitCoordsF12 := [ElementCoordinates(x[1], [1,s1]) cat ElementCoordinates(x[2], [1,s1]) : x in UnitCoordsK2Basis];
    Norms1 := [ u[1]^2+u[2]^2*y1-u[3]^2*y2-u[4]^2*y1*y2+(2*u[1]*u[2]-2*u[3]*u[4]*y2)*s1 :u in UnitCoordsF12];
    Norms2 := [ u[1]^2+u[3]^2*y2-u[2]^2*y1-u[4]^2*y1*y2+(2*u[1]*u[3]-2*u[2]*u[4]*y1)*s2 :u in UnitCoordsF12];

    UnitCoordsK3Basis := [ElementCoordinates(g,[1,e3]): g in UpStairsUf];
    UnitCoordsF13 := [ElementCoordinates(x[1], [1,s1]) cat ElementCoordinates(x[2], [1,s1]) : x in UnitCoordsK3Basis];
    Norms3 := [ u[1]^2+u[3]^2*y3-u[2]^2*y1-u[4]^2*y1*y3+(2*u[1]*u[3]-2*u[2]*u[4]*y1)*s3 :u in UnitCoordsF13];


    for chi in SCR[1] do
        Match2 := [tau : tau in SCR[2] | chi`CondExp eq tau`CondExp];
        Match3 := [tau : tau in SCR[3] | chi`CondExp eq tau`CondExp];
        isIso2, iso2 := IsIsomorphic(Codomain(chi`Character`Map), Codomain(SCR[2,1]`Character`Map));
        isIso3, iso3 := IsIsomorphic(Codomain(chi`Character`Map), Codomain(SCR[3,1]`Character`Map));

        for t in [1..#Norms1] do
            Match2 := [tau: tau in Match2 | iso2(chi`Character(Norms1[t])) eq tau`Character(Norms2[t])];
            Match3 := [tau: tau in Match3 | iso3(chi`Character(Norms1[t])) eq tau`Character(Norms3[t])];
        end for;      
        if #Match2 eq 1 and #Match3 eq 1 then
            Append(~TriplyImprimitiveTypes, TriplyImprimitiveType([
                chi`Character, Match2[1]`Character, Match3[1]`Character
            ], chi`BaseField));
        elif not (#Match2 eq 0 and #Match3 eq 0) then
            vprint ECITypes : "ERROR in matching triply imprimitive types";
            assert false;
        end if;
    end for;

    return TriplyImprimitiveTypes;
end function;


intrinsic SupercuspidalRamified(F, K::SeqEnum[FldPad]) -> SeqEnum[SCRInType] 
{Returns some SCR types}
    p := Prime(F);
    require p in [2, 3] : "Supercuspidal ramified inertial types only exist for 2-adic and 3-adic fields";
    if p eq 2 then
        if AbsoluteInertiaDegree(F) mod 2 eq 0 then
            require #K in [1, 2, 3] : "SCR must be induced from a tuple of 1 to 3 fields";
            // check all three fields are a Selmer orbit
            if #K eq 3 then
                disc1 := Discriminant(DefiningPolynomial(K[1]));
                disc2 := Discriminant(DefiningPolynomial(K[2]));
                require IsSquare(K[3]!(disc1 * disc2)) : "The compositum of the three given fields must form a biquadratic extension";
            end if;

            // now we match every SCR type from K[1] to the others
            if #K eq 1 then return SupercuspidalRamified(F, K[1]);
            else
                return SCRMatched(F, K, []);
            end if;
        else
            require #K eq 1 : "SCR must be induced from a single field";
            return SupercuspidalRamified(F, K);
        end if;
    else // p eq 3 then 
        require #K eq 1 : "SCR must be induced from a single field";
        return SupercuspidalRamified(F, K);
    end if;
end intrinsic;

intrinsic SupercuspidalRamified(F::FldPad : QuadExt := [], Twist := []) -> SeqEnum[SCRInType]
{Returns all SCR types}
    p := Prime(F);
    if #QuadExt eq 0 or #Twist eq 0 then
        QuadExt, Twist := AllQuadraticExtensions(F : Selmer := false);
    end if;
    vprintf ECITypes: "Computed all quadratic extensions (%o)\n", #Twist;

    SCR := [(RamificationDegree(K, F) eq 2) select SupercuspidalRamified(F, K) else [] : K in QuadExt];

    if p eq 2 and AbsoluteInertiaDegree(F) mod 2 eq 0 then
        Sel, FtoSel := pSelmerGroup(2,F);
        SeltoF := Inverse(FtoSel);
        Triples := {};
        for i,j in [1..#Twist] do
            if i eq j then continue; end if; 
            x := FtoSel(Twist[i]);
            y := FtoSel(Twist[j]);
            z := x*y;
            k := [l : l in [1..#Twist] | FtoSel(Twist[l]) eq z ][1];
            if IsEmpty({tau`CondExp: tau in SCR[i]} meet {tau`CondExp: tau in SCR[j]} meet {tau`CondExp: tau in SCR[k]}) then continue; end if;
            trip := {i,j,k};
            if #trip eq 3 then 
                Include(~Triples,trip);
            end if;
        end for;

        TriplyImprimitiveTypes := [];
        for triple in Triples do
            ThisTriply := SCRMatched(F, [QuadExt[i] : i in triple], [SCR[i] : i in triple]);
            for i in [1 .. #ThisTriply] do
                ThisTriply[i]`Indexes := Sort(SetToSequence(triple));
            end for;
            TriplyImprimitiveTypes cat:= ThisTriply;
        end for;

        return TriplyImprimitiveTypes, Twist;
    else 
        return &cat SCR, Twist;
    end if;
end intrinsic;

//////// EXCEPTIONAL TYPES ////////

//This function produces the 2-Selmer Group of L as a Gal(L/F) module
function SelmerGaloisModule (F,L)
    assert IsNormal(L,F);
    F2 := GF(2);
    Gal,GaltoAut := AutomorphismGroup(L,F);
    Sel,LtoSel := pSelmerGroup(2,L);
    n := #Generators(Sel);
    Operators := [ScalarMatrix(GF(2),n,1)];
    ListOfGens := [Sel.i : i in [1 .. n]];

    for t in Generators(Gal) do
        M := [];
        g := GaltoAut(t);

        for z in ListOfGens do
            y := ChangePrecision(Inverse(LtoSel)(z), Precision(L));
            Append(~M, ElementToSequence(LtoSel(g(y))));
        end for;
        Append(~Operators, Matrix(F2,M));
    end for;
    GSel := GModule(Gal, Operators);
    return GSel, Sel, Inverse(LtoSel), Gal, GaltoAut;
end function;

function ExceptionalTypes(F, L)
    // require IsNormal(L,F) : "The extension L/F must be normal";
    // require ((AbsoluteInertiaDegree(F) mod 2 eq 0) and (Degree(L, F) eq 3)) 
    //     or (
    //         (AbsoluteInertiaDegree(F) mod 2 eq 1) 
    //         and (Degree(L, F) eq 6) 
    //         and (InertiaDegree(L, F) mod 2 eq 0)
    //     ) : "Invalid degree conditions for L/F";

    R<X> := PolynomialRing(L);
    GSel, Sel, SeltoL, Gal, GaltoAut := SelmerGaloisModule(F,L);

    // Look for an element rho of order 3 in the Galois group
    for tau in Gal do
        if Order(tau) eq 3 then rho := GaltoAut(tau); break; end if;
    end for;

    SelOrbits := [M: M in MinimalSubmodules(GSel) | Dimension(M) eq 2];
    vprintf ECITypes : "%o Selmer orbits\n", #SelOrbits;

    ExceptionalChars:=[* *];
    i := 0;
    for orbit in SelOrbits do
        i +:= 1;
        Polynomials := [];
        roots := [];
        g := GaltoAut(Identity(Gal));
        for i in [1..3] do
            g := g*rho;
            z := g(ChangePrecision(SeltoL(Sel!ElementToSequence(GSel!orbit.1)), Precision(L)));
            Append(~Polynomials, X^2 - R!z);
        end for;
        K1 := SplittingField(Polynomials[1]);

        K1X<x> := PolynomialRing(K1);
        E := SplittingField(K1X!Polynomials[2]);

        // The orbit will only give exceptional types if either
        // (a) L/F is cubic, or
        // (b) E/F has ramification degree 12 and is Galois with group S4
        viableOrbit := Degree(L,F) eq 3;
        time GalE, GalEtoAut := AutomorphismGroup(E,F);
        GalEGens := [GalEtoAut(tau) : tau in Generators(GalE)];
        if not viableOrbit then
            viableOrbit := RamificationDegree(E,F) eq 12 and IsIsomorphic(GalE,Sym(4));
        end if;

        // In our experience the orbit is always viable (we need a proof of this)
        if viableOrbit then
            // Initialize character conditions
            p, ram_deg, in_deg, pi, N := BaseValues(L);
            Cond, pi, Gal_L_K1, y := ExtValues(L,K1);
            f := Max(N-Cond, 2*Cond);
            c := Cond;

            UGroups, UMaps, ULift := UComplex(L, f);
            G := UGroups[1];
            llift:=ULift;

            CGroups1, CMaps1, CLift1 := ConComplex(L, K1, f);
            proj := Inverse(CLift1);
            bar_y2 := 2*proj(y);

            VarepsGenerators := [K1!llift(g) : g in Generators(G) | not IsIdentity(proj(K1!llift(g)))];
            Elements := [proj(g) : g in VarepsGenerators];
            Values := [2 : g in VarepsGenerators];
            
            // We are computing triply imprimitive => bar_y2 goes to 0
            Append(~Elements, bar_y2);
            Append(~Values, 0);

            time Uf, UpStairsUf := OptimalNorms(E,K1,#CGroups1);

            Uf1:=[proj(g): g in Uf];
            Elements := Elements cat [2*g : g in Uf1];
            Values := Values cat [0 : i in [1 .. #Uf1]];

            piE := UniformizingElement(E);

            time for mu in GalEGens do
                muUf1:=[proj(Norm(mu(g),K1)): g in UpStairsUf];
                Elements := Elements cat [Uf1[i] - muUf1[i] : i in [1 .. #Uf1]];
                Values := Values cat [0 : i in [1 .. #Uf1]];

                x := piE / mu(piE);
                Elements := Elements cat [proj(Norm(x, K1))];
                Values := Values cat [0];
            end for;
            
            characters := FastCharactersOfPrimePowerOrder(
                CGroups1[1], 2, 2, CMaps1, CLift1 : Elements:=Elements, Values:=Values
            );
            vprintf ECITypes : "Selmer orbit #%o yields %o exceptional types\n", i, #characters;

            if not IsEmpty(characters) then 
                typesFromOrbit := [ExceptionalType(phi, F, L) : phi in characters];
                Append(~ExceptionalChars, typesFromOrbit);
            end if;
            // print("------------------");
        end if;
         end for;
    return ExceptionalChars;
end function;

function ExceptionalTypesTriply(F, L)
    assert Degree(L, F) eq 3;

    return ExceptionalTypes(F, L);
end function;

function ExceptionalTypesSimply(F)
    Fx<x>:=PolynomialRing(F);
    Fprime := UnramifiedExtension(F,2);
    for l in [1..3] do 
        L := FieldOfFractions(AllExtensions(Fprime, 3)[l]);
        if IsNormal(L,F) then break; end if;
    end for;
    return ExceptionalTypes(F, L);
end function;

intrinsic InertialTypes(F :: FldPad : SkipExceptionals := false) 
    -> SeqEnum[FldPadElt],
       SeqEnum[PrincipalSeriesIT],
       SeqEnum[SCUInType],
       SeqEnum[SeqEnum[SCRInType]],
       SeqEnum,
       SeqEnum
{Compute all inertia types attached to elliptic curves over the field F. Returns:
    - A list of values in F giving all used quadratic twists
    - A list of Principal Series Types
    - A list of Supercuspidal Unramified Types
    - A list of lists, each with Supercuspidal Ramified Types of thTriply Imprimitive Inertia Type of the field
         Unramified extension defined by the polynomial x^2 + x + 1 + O(2^100) 
    over 2-adic field mod 2^100
    of conductor exponent 8
    with 3 underlying characters of order 4 and conductor exponents [6, 5, 5],
e twist #i
    - A list of Exceptional Types of size 8
    - A list of Exceptional Types of size 24
}
    c := 0;
    QuadExt,Twist := AllQuadraticExtensions(F : Selmer := false);
    vprintf ECITypes: "Computed all quadratic extensions (%o)\n", #Twist;
    
    p, ram_deg, in_deg, pi, N := BaseValues(F);
    ff := Floor(N/2);
    groups, maps, lift := UComplex(F, ff);
    vprintf ECITypes: "N=%o\n", N;

    PS := PrincipalSeries(F : MyComplex := [*groups, maps, lift*]);
    vprintf ECITypes: "Computed %o principal series types\n", #PS;

    i := 1;
    SCR := [* [] : _ in [1..#Twist] *];
    for t in [1..#QuadExt] do
        K:=QuadExt[t];
        i;
        Cond, pi, Gal, y := ExtValues(F,K);
        c := Cond;
        if Cond eq 0 then
            SCU := SupercuspidalUnramified(F,K,ff);
            vprintf ECITypes: "Computed %o supercuspidal unramified types\n", #SCU;
        else 
            f := Max(N-Cond, 2*Cond);
            vprintf ECITypes: "f=%o\n", f;
            vprintf ECITypes: "c=%o\n", c;

            G := groups[1];
            llift:=lift;

            VarepsGenerators := {K!llift(g) : g in Generators(G)};
            SCR_K := InternalSCR(F, K, f, c, VarepsGenerators);
            SCR[t] := SCR_K;
            vprintf ECITypes: "Computed %o supercuspidal ramified types for quadratic extension #%o\n", #SCR_K, i;
        end if;
        i +:= 1;
    end for;

    Ex24:=[* *];
    Ex8:=[* *];
    if p eq 2 and not SkipExceptionals then
        if (in_deg mod 2 eq 0) then 
            for j in [1..3] do
                L:=FieldOfFractions(AllExtensions(F,3)[j]);
                Ex_L:=ExceptionalTypesTriply(F,L);
                Append(~Ex24, Ex_L);
                vprintf ECITypes: "Computed %o exceptional types of size 24 for cubic extension #%o\n", &+([#c : c in Ex_L] cat [0]), j;
            end for;
            L := FieldOfFractions(AllExtensions(F,3)[4]);
            Ex8 := ExceptionalTypesTriply(F,L);
            vprintf ECITypes: "Computed %o exceptional types of size 8\n", &+([#c : c in Ex8] cat [0]);
        else 
            Ex24 := ExceptionalTypesSimply(F);
            vprintf ECITypes: "Computed %o exceptional types of size 24\n", &+([#c : c in Ex24] cat [0]);
        end if;
    end if;

    return Twist, PS, SCU, SCR, Ex8, Ex24;
end intrinsic;