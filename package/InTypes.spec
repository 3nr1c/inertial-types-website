declare verbose InTypes, 3;

import "utils.m" : AllQuadraticExtensions, 
                   OptimalNorms, 
                   IsValidExceptionalExtension, 
                   ElementCoordinates,
                   CmpCondExp;
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



////// SUPERCUSPIDAL UNRAMIFIED TYPES /////
function InternalSCU(F, K, f : Order := 0, TrivialOn := [], QuadraticOn := [])
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

    return InternalSCU(F, K, f : Order := Order, TrivialOn := TrivialOn, QuadraticOn := QuadraticOn);
end intrinsic;

///// SUPERCUSPIDAL RAMIFIED ////
function InternalSCR2(F, K, f, c, VarepsGenerators : KernelElements := [])
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

function InternalSCR3(F, K, f, c, VarepsGenerators)
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
        return InternalSCR2(F, K, f, c, VarepsGenerators);
    elif p eq 3 then
        return InternalSCR3(F, K, f, c, VarepsGenerators);
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

function InternalSCRMatched(F, K, SCR)
// F::FldPad, K::SeqEnum[FldPad], SCR::SeqEnum[SCRInType]
    assert #K in [2, 3];

    // This list will contain the types
    TriplyImprimitiveTypes := [];
    i1s := {};
    i2s := {};
    i3s := {};

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
    if #SCR[1] eq 0 or #SCR[2] eq 0 or #SCR[3] eq 0 then
        return TriplyImprimitiveTypes, [], [], [];// = []
    end if;

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
    Norms1 := [ u[1]^2+u[2]^2*y1-u[3]^2*y2-u[4]^2*y1*y2+(2*u[1]*u[2]-2*u[3]*u[4]*y2)*s1 : u in UnitCoordsF12];
    Norms2 := [ u[1]^2+u[3]^2*y2-u[2]^2*y1-u[4]^2*y1*y2+(2*u[1]*u[3]-2*u[2]*u[4]*y1)*s2 : u in UnitCoordsF12];

    UnitCoordsK3Basis := [ElementCoordinates(g,[1,e3]): g in UpStairsUf];
    UnitCoordsF13 := [ElementCoordinates(x[1], [1,s1]) cat ElementCoordinates(x[2], [1,s1]) : x in UnitCoordsK3Basis];
    Norms3 := [ u[1]^2+u[3]^2*y3-u[2]^2*y1-u[4]^2*y1*y3+(2*u[1]*u[3]-2*u[2]*u[4]*y1)*s3 :u in UnitCoordsF13];

    isIso3, iso3 := IsIsomorphic(Codomain(SCR[1,1]`Character`Map), Codomain(SCR[3,1]`Character`Map));
    isIso2, iso2 := IsIsomorphic(Codomain(SCR[1,1]`Character`Map), Codomain(SCR[2,1]`Character`Map));
    for i1 in [1..#SCR[1]] do
        chi := SCR[1,i1];

        chiNorms1 := [];
        quadraticOnNorms := true;
        for t in [1..#Norms1] do
            chiNm := chi`Character(Norms1[t]);
            Append(~chiNorms1, chiNm);
            if not IsIdentity(2*chiNm) then
                quadraticOnNorms := false;
                break;
            end if;
        end for;
        if not quadraticOnNorms then 
            continue;
        end if;

        found2 := false;
        i2 := 0;
        while (not found2) and (i2 lt #SCR[2]) do
            i2 +:= 1;
            tau := SCR[2,i2];
            if chi`CondExp eq tau`CondExp then
                found2 := true;
                for t in [1..#Norms1] do
                    chiNm := chiNorms1[t];
                    tauNm := tau`Character(Norms2[t]);
                    // found2 := found2 and IsIdentity(2*chiNm);
                    found2 := found2 and IsIdentity(2*tauNm);
                    found2 := found2 and iso2(chiNm) eq tauNm;
                    if not found2 then
                        break;
                    end if;
                end for;
            else 
                found2 := false;
            end if;
        end while;
        if not found2 then continue; end if;

        found3 := false;
        i3 := 0;
        while (not found3) and (i3 lt #SCR[3]) do
            i3 +:= 1;
            tau := SCR[3,i3];
            if chi`CondExp eq tau`CondExp then
                found3 := true;
                for t in [1..#Norms1] do
                    chiNm := chiNorms1[t];
                    tauNm := tau`Character(Norms3[t]);
                    // found3 := found3 and IsIdentity(2*chiNm);
                    found3 := found3 and IsIdentity(2*tauNm);
                    found3 := found3 and iso3(chiNm) eq tauNm;
                    if not found3 then
                        break;
                    end if;
                end for;
            else 
                found3 := false;
            end if;
        end while;
        
        if found2 and found3 then
            // if InFields then
            //     L := chi`InField;
            // else
            //     L := 0;
            // end if;
            Append(~TriplyImprimitiveTypes, TriplyImprimitiveType([
                chi`Character, SCR[2,i2]`Character, SCR[3,i3]`Character
            ], chi`BaseField));
            Include(~i1s, i1);
            Include(~i2s, i2);
            Include(~i3s, i3);
        end if;
    end for;

    return TriplyImprimitiveTypes, SetToSequence(i1s), SetToSequence(i2s), SetToSequence(i3s);
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
                return InternalSCRMatched(F, K, []);
            end if;
        else
            require #K eq 1 : "SCR must be induced from a single field";
            return SupercuspidalRamified(F, K[1]);
        end if;
    else // p eq 3 then 
        require #K eq 1 : "SCR must be induced from a single field";
        return SupercuspidalRamified(F, K[1]);
    end if;
end intrinsic;

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

procedure InFieldsTwist(~Tau, Twist : aut := 1)
    queue := [1..#Tau];
    while #queue gt 0 do
        vprintf InTypes,3 : "InType: Compute InField for #%o\n", queue[1];
        tau := Tau[queue[1]]; 
        Remove(~queue, 1);
        L := InField(tau); 

        expected := (#Twist + 1)/(2*aut) - 1;
        // We will enter here only when p=2
        if expected le 0 then continue; end if;
        M := BaseField(L);
        Mx<x> := PolynomialRing(M);
        disc := Discriminant(L, M);
        for s in Twist do
            if expected eq 0 then break; end if;
            sdisc := M!s*disc;
            Ls := SplittingField(x^2 - sdisc);
            tau2, j := FindInType(Ls, [Tau[k] : k in queue]);
            if not IsNull(tau2) and 
                RamificationDegree(Ls, tau2`BaseField) eq SemistabilityDefect(tau2)
            then
                vprintf InTypes,3 : "InTypes: Twist to find InField #%o\n", queue[j];
                tau2`InField := Ls;
                Remove(~queue, j);
                expected := expected - 1;
            end if;
        end for;
    end while;
end procedure;

intrinsic SupercuspidalRamified(F::FldPad : QuadExt := [], Twist := [], InFields:=InFields) -> SeqEnum[SCRInType]
{Returns all SCR types}
    p := Prime(F);
    if #QuadExt eq 0 or #Twist eq 0 then
        QuadExt, Twist := AllQuadraticExtensions(F : Selmer := false);
        vprintf InTypes, 1: "InTypes: Computed all quadratic extensions (%o)\n", #Twist;
    end if;

    SCR := [];
    t := Cputime();
    for i in [1..#QuadExt] do
        K := QuadExt[i];
        Append(~SCR, (RamificationDegree(K, F) eq 2) select SupercuspidalRamified(F, K) else []);
    end for;
    vprintf InTypes, 1: "InTypes: Computed %o SCR types in %os\n", &+[#c : c in SCR], Cputime(t);

    if p eq 2 and AbsoluteInertiaDegree(F) mod 2 eq 0 then
        vprint InTypes : "Grouping triply imprimitive types...";
        t := Cputime();

        // generate triples of indices {i,j,k} such that
        // the twists Twist[i],[j],[k] form a Selmer submodule of dim 2
        Triples := [];
        // We are free to take i<j. For k, notice that if i*j=k < j, then 
        // we would have found {i,j,k} by doing j=i*k. Same if i*j=k < i.
        for i in [1..#Twist], j in [i+1..#Twist] do
            x := Twist[i];
            y := Twist[j];
            for k in [j+1..#Twist] do
                if IsSquare(x*y*Twist[k]) then
                    Append(~Triples, [i,j,k]);
                    break;
                end if;
            end for;
        end for;
        vprintf InTypes, 1: "InTypes: We have %o field triples\n", #Triples;

        TriplyImprimitiveTypes := [];
        for triple in Triples do
            ThisTriply, i1s, i2s, i3s := InternalSCRMatched(F, 
                [QuadExt[i] : i in triple], [SCR[i] : i in triple]);
            vprintf InTypes, 2: "InTypes: Triple {%o,%o,%o}: found %o grouped types\n", 
                triple[1], triple[2], triple[3], #ThisTriply;

            if false and InFields and #ThisTriply gt 0 then
                t1 := Cputime();
                InFieldsTwist(~ThisTriply, Twist : aut := 4);
                vprintf InFields, 2 : "InFields: Computed %o inertia fields in %os\n", #ThisTriply, Cputime(t1);  
            end if;

            for i in [1 .. #ThisTriply] do
                tau := ThisTriply[i];
                tau`Indexes := triple;
                Append(~TriplyImprimitiveTypes, tau);
            end for;
            for i1 in Reverse(Sort(i1s)) do Remove(~SCR[triple[1]], i1); end for;
            for i2 in Reverse(Sort(i2s)) do Remove(~SCR[triple[2]], i2); end for;
            for i3 in Reverse(Sort(i3s)) do Remove(~SCR[triple[3]], i3); end for;
        end for;
        // [#c : c in SCR];

        if InFields then
            vprintf InTypes, 1: "InTypes: Grouping triply imprimitive types (with InFields) took %os\n", Cputime(t);
        else
            vprintf InTypes, 1: "InTypes: Grouping triply imprimitive types took %os\n", Cputime(t);
        end if;

        return TriplyImprimitiveTypes, Twist;
    else 
        if InFields then
            for i in [1..#SCR] do
                if #SCR[i] eq 0 then continue; end if;
                t := Cputime();
                InFieldsTwist(~SCR[i], Twist : aut := 2);
                vprintf InTypes, 1: "InTypes: Computation of %o inertia fields took %os\n", #SCR[i], Cputime(t);
            end for;
        end if;
        return &cat SCR, Twist;
    end if;
end intrinsic;

//////// EXCEPTIONAL TYPES ////////


function InternalExceptionalTypes(F, L : InducingFields := [], InFields := false)
    // require IsNormal(L,F) : "The extension L/F must be normal";
    // require ((AbsoluteInertiaDegree(F) mod 2 eq 0) and (Degree(L, F) eq 3)) 
    //     or (
    //         (AbsoluteInertiaDegree(F) mod 2 eq 1) 
    //         and (Degree(L, F) eq 6) 
    //         and (InertiaDegree(L, F) mod 2 eq 0)
    //     ) : "Invalid degree conditions for L/F";

    R<X> := PolynomialRing(L);
    GSel, Sel, SeltoL, Gal, GaltoAut := SelmerGaloisModule(F,L);

    // Needed to compute inertia fields
    FSel, FtoSel := pSelmerGroup(2, F);
    SeltoF := Inverse(FtoSel);
    Twist := [SeltoF(s) : s in FSel];

    // Look for an element rho of order 3 in the Galois group
    for tau in Gal do
        if Order(tau) eq 3 then rho := GaltoAut(tau); break; end if;
    end for;

    SelOrbits := [M: M in MinimalSubmodules(GSel) | Dimension(M) eq 2];
    vprintf InTypes, 1: "InTypes: Computing exceptional types from %o Selmer orbits\n", #SelOrbits;

    Exceptionals:=[];
    i := 0;
    for orbit in SelOrbits do
        i +:= 1;
        Polynomials := [];
        roots := [];
        g := GaltoAut(Identity(Gal));
        for ii in [1..3] do
            g := g*rho;
            z := g(ChangePrecision(SeltoL(Sel!ElementToSequence(GSel!orbit.1)), Precision(L)));
            Append(~Polynomials, X^2 - R!z);
        end for;
        if #InducingFields gt 0 then
            if not &or[HasRoot(f, K) : f in Polynomials, K in InducingFields] then
                continue;
            end if;
        end if;
        K1 := SplittingField(Polynomials[1]);
        K2 := SplittingField(Polynomials[2]);
        K3 := SplittingField(Polynomials[3]);

        K1X<x> := PolynomialRing(K1);
        E := SplittingField(K1X!Polynomials[2]);
        ET<T> := PolynomialRing(E);
        y1 := Sqrt(E!(-Coefficient(Polynomials[1],0)));
        y2 := Sqrt(E!(-Coefficient(Polynomials[2],0)));

        // The orbit will only give exceptional types if either
        // (a) L/F is cubic, or
        // (b) E/F has ramification degree 12 and is Galois with group S4
        viableOrbit := Degree(L,F) eq 3;
        GalE, GalEtoAut := AutomorphismGroup(E,F);
        GalEGens := [GalEtoAut(tau) : tau in Generators(GalE)];
        if not viableOrbit then
            // viableOrbit := RamificationDegree(E,F) eq 12 and IsIsomorphic(GalE,Sym(4));
            viableOrbit := RamificationDegree(E,F) eq 12 and #GalE eq 24;
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

            Uf, UpStairsUf := OptimalNorms(E,K1,#CGroups1);

            Uf1:=[proj(g): g in Uf];
            Elements := Elements cat [2*g : g in Uf1];
            Values := Values cat [0 : i in [1 .. #Uf1]];

            piE := UniformizingElement(E);

            for mu in GalEGens do
                muUf1:=[proj(Norm(mu(g),K1)): g in UpStairsUf];
                Elements := Elements cat [Uf1[i] - muUf1[i] : i in [1 .. #Uf1]];
                Values := Values cat [0 : i in [1 .. #Uf1]];

                x := piE / mu(piE);
                Elements := Elements cat [proj(Norm(x, K1))];
                Values := Values cat [0];
            end for;
            
            OrbitTypes := [ExceptionalType(chi, F, L, [K1, K2, K3]) :
                chi in FastCharactersOfPrimePowerOrder(
                    CGroups1[1], 2, 2, CMaps1, CLift1 : Elements:=Elements, Values:=Values
                )
            ];
            vprintf InTypes, 1: "InTypes: Selmer orbit #%o yields %o exceptional types\n", i, #OrbitTypes;

            if #OrbitTypes eq 0 then continue; end if;
            if not InFields then
                Exceptionals := Exceptionals cat OrbitTypes;
                continue;
            end if;

            t := Cputime();
            E2 := ChangePrecision(E,Max(Precision(F), 60));
            UE, UEtoE := UnitGroup(E2);
            EtoUE := Inverse(UEtoE);
            Utors := sub<UE|[g : g in Generators(UE)| not IsZero(Order(g))]>;
            Utorsgens := SetToSequence(Generators(Utors));
            Utorsnorm := [Norm(UEtoE(g), K1) : g in Utorsgens];
            piE2 := EtoUE(UniformizingElement(E2));
            vprintf InTypes, 1: "InTypes: Computed Nm(M) in %os. Computing inertia fields...\n", Cputime(t);

            while #OrbitTypes gt 0 do
                // order types by conductor exponent to speed up class field computation
                OrbitTypes := Sort(OrbitTypes, CmpCondExp);
                
                tau := OrbitTypes[1];
                chi := tau`Character;
                //Exclude(~OrbitTypes, tau);

                ker := Kernel(Homomorphism(Utors, Codomain(chi`Map), Utorsgens, 
                    [chi(Nmg) : Nmg in Utorsnorm]
                ));
                Norms := sub<UE|ker, piE2>;
                t := Cputime();
                M := ClassField(UEtoE, Norms);
                vprintf InTypes, 1: "InTypes: Computation of one inertia field took %os (v(N) = %o)\n", Cputime(t), tau`CondExp;
                //DefiningPolynomial(M,F);
                
                tau := ExceptionalType(chi, F, L);
                tau`InField := M;
                //Append(~Exceptionals, tau);
                
                // If there are still some types, twist field and eliminate some
                Mdisc := Discriminant(M, E);
                t := Cputime();
                for s in FSel do
                    if #OrbitTypes eq 0 then break; end if;
                    //if IsIdentity(s) then continue; end if;
                    Mdisc_s := ChangePrecision(E!(SeltoF(s))*Mdisc, Precision(E));
                    Ms := SplittingField(T^2 - Mdisc_s);
                    tau2, j := FindInType(Ms, OrbitTypes);
                    if not IsNull(tau2) then
                        tau2`InField := Ms;
                        Remove(~OrbitTypes, j);
                        Append(~Exceptionals, tau2);
                    end if;
                end for;
                vprintf InTypes, 1: "InTypes: Computation of inertia fields of twists took %os\n", Cputime(t);
            end while;

            //Exceptionals cat:= [ExceptionalType(phi, F, L) : phi in characters];
            // print("------------------");
        end if;
    end for;
    return Exceptionals;
end function;

function ExceptionalTypesTriply(F, L : InFields := false)
    assert Degree(L, F) eq 3;

    return InternalExceptionalTypes(F, L : InFields := InFields);
end function;

function ExceptionalTypesSimply(F : InFields := false)
    Fx<x>:=PolynomialRing(F);
    Fprime := UnramifiedExtension(F,2);
    for l in [1..3] do 
        L := FieldOfFractions(AllExtensions(Fprime, 3)[l]);
        if IsNormal(L,F) then break; end if;
    end for;
    return InternalExceptionalTypes(F, L : InFields := InFields);
end function;


intrinsic ExceptionalTypes(F::FldPad : InFields := false) 
    -> SeqEnum[ExceptionalInType], SeqEnum[ExceptionalInType]
{Return all exceptional inertia types of F}
    require Prime(F) eq 2 : "There are no exceptional types for p>2.";
    Ex24:=[];
    Ex8:=[];
    if (AbsoluteInertiaDegree(F) mod 2 eq 0) then 
        for j in [1..3] do
            L:=FieldOfFractions(AllExtensions(F,3)[j]);
            Ex_L:=ExceptionalTypesTriply(F,L : InFields := InFields);
            Ex24 cat:= Ex_L;
            vprintf InTypes, 1: "InTypes: Computed %o exceptional types of size 24 for cubic extension #%o\n", #Ex_L, j;
        end for;
        L := FieldOfFractions(AllExtensions(F,3)[4]);
        Ex8 := ExceptionalTypesTriply(F,L : InFields := InFields);
        vprintf InTypes, 1: "InTypes: Computed %o exceptional types of size 8\n", #Ex8;
    else 
        Ex24 := ExceptionalTypesSimply(F : InFields := InFields);
        vprintf InTypes, 1: "InTypes: Computed %o exceptional types of size 24\n", #Ex24;
    end if;

    return Ex8, Ex24;
end intrinsic;

intrinsic ExceptionalTypes(F::FldPad, L::FldPad : InFields := false) -> SeqEnum[ExceptionalInType]
{Return all exceptional inertia types of F which first become imprimitive over L}
    require Prime(F) eq 2 : "There are no exceptional types for p>2.";
    assert IsValidExceptionalExtension(F, L);

    return InternalExceptionalTypes(F, L : InFields := InFields);
end intrinsic;

intrinsic ExceptionalTypes(F::FldPad, L::FldPad, K::FldPad : InFields := InFields) -> SeqEnum[ExceptionalInType]
{Return all exceptional inertia types of F which first become imprimitive over L, and are 
induced from a quartic character of K}
    require Prime(F) eq 2 : "There are no exceptional types for p>2.";
    assert IsValidExceptionalExtension(F, L);
    
    return InternalExceptionalTypes(F, L : InducingFields := [K], InFields := InFields);
end intrinsic;

intrinsic InTypes(F :: FldPad : SkipExceptionals := false, InFields := false) 
    -> SeqEnum[PrincipalSeriesIT],
       SeqEnum[SCUInType],
       SeqEnum[SCRInType],
       SeqEnum[ExceptionalInType],
       SeqEnum[ExceptionalInType],
       SeqEnum[FldPadElt]
{Compute all inertia types attached to elliptic curves over the field F. Returns:
    - A list of Principal Series Types
    - A list of Supercuspidal Unramified Types
    - A list of Supercuspidal Ramified Types
    - A list of Exceptional Types of size 8
    - A list of Exceptional Types of size 24
    - A list of values in F giving all used quadratic twists
}
    require Type(Precision(F)) eq RngIntElt : "Precision of field must be finite, please use ChangePrecision(F,100);";
    c := 0;
    QuadExt,Twist := AllQuadraticExtensions(F : Selmer := true);
    vprintf InTypes, 1: "InTypes: Computed all quadratic extensions (%o)\n", #Twist;
    
    p, ram_deg, in_deg, pi, N := BaseValues(F);
    ff := Floor(N/2);
    groups, maps, lift := UComplex(F, ff);
    vprintf InTypes, 1: "InTypes: N=%o\n", N;

    PS := Sort(PrincipalSeries(F : MyComplex := [*groups, maps, lift*]), CmpCondExp);
    vprintf InTypes, 1: "InTypes: Computed %o principal series types\n", #PS;

    if InFields then
        t := Cputime();
        for i in [1..#PS] do
            PS[i]`InField := InField(PS[i]);
        end for;
        vprintf InTypes, 1: "InTypes: Computation of %o inertia fields took %os\n", #PS, Cputime(t);
    end if;


    SCU := Sort(SupercuspidalUnramified(F), CmpCondExp);
    vprintf InTypes, 1: "InTypes: Computed %o supercuspidal unramified types\n", #SCU;
    
    if InFields then
        t := Cputime();
        InFieldsTwist(~SCU, Twist : aut:=2);
        // for i in [1..#SCU] do
        //     SCU[i]`InField := InField(SCU[i]);
        // end for;
        vprintf InTypes, 1: "InTypes: Computation of %o inertia fields took %os\n", #SCU, Cputime(t);
    end if;


    SCR := Sort(SupercuspidalRamified(F : QuadExt:=QuadExt, Twist:=Twist, InFields:=InFields), CmpCondExp);
    vprintf InTypes, 1: "InTypes: Computed %o supercuspidal ramified types\n", #SCR;    
        
    Ex24:=[];
    Ex8:=[];
    if p eq 2 and not SkipExceptionals then
        if (in_deg mod 2 eq 0) then 
            for j in [1..3] do
                L:=FieldOfFractions(AllExtensions(F,3)[j]);
                Ex_L:=ExceptionalTypesTriply(F,L : InFields := InFields);
                Ex24 := Ex24 cat Ex_L;
                vprintf InTypes, 1: "InTypes: Computed %o exceptional types of size 24 for cubic extension #%o\n", #Ex_L, j;
            end for;

            L := FieldOfFractions(AllExtensions(F,3)[4]);
            Ex8 := Sort(ExceptionalTypesTriply(F,L : InFields := InFields), CmpCondExp);
            vprintf InTypes, 1: "InTypes: Computed %o exceptional types of size 8\n", #Ex8;
        else 
            Ex24 := ExceptionalTypesSimply(F : InFields := InFields);
            vprintf InTypes, 1: "InTypes: Computed %o exceptional types of size 24\n", #Ex24;
        end if;
        Ex24 := Sort(Ex24, CmpCondExp);
    end if;

    return PS, SCU, SCR, Ex8, Ex24, Twist;
end intrinsic;


intrinsic InTypes(F :: FldNum, p :: RngOrdIdl) -> .
{}
    Fp, m := Completion(F, p);
    Fp100 := ChangePrecision(Fp, 100);

    return InTypes(Fp100);
end intrinsic

intrinsic InTypes(R :: RngOrd, p :: RngOrdIdl) -> .
{}
    F := FieldOfFractions(R);
    Fp, m := Completion(F, p);
    Fp100 := ChangePrecision(Fp, 100);

    return InTypes(Fp100);
end intrinsic
