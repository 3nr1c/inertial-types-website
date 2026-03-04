declare verbose ECITypes, 1;

import "utils.m" : AllQuadraticExtensions, OptimalNorms;
import "sequences.m" : UComplex, ConComplex, BaseValues, ExtValues;
import "characters.m" : FastCharactersOfOrder, FastCharactersOfPrimePowerOrder;


function PrincipalSeries(F, f : MyComplex:=[* *])
    if #MyComplex eq 3 then
        groups := MyComplex[1];
        maps := MyComplex[2];
        lift := MyComplex[3];
    else
        groups, maps, lift := UComplex(F, f);
    end if;
    
    PS := [];
    for n in {2, 3, 4, 6} do
        PS cat:= [
            PrincipalSeriesType(phi) 
            : phi in FastCharactersOfOrder(groups[1], n, maps, lift)
        ];
    end for;

    return PS;
end function;


function SupercuspidalUnramified(F, K, f)
    if Valuation(Discriminant(K,F)) gt 0 then
        error Error("The extension K|F is not unramified");
    end if;

    groups, maps, lift := ConComplex(F, K, f);
    SCU := [];
    for n in {3, 4, 6} do
        SCU cat:= [
            SupercuspidalUnramifiedType(phi, F)
            : phi in FastCharactersOfOrder(groups[1], n, maps, lift)
        ];
    end for;

    return SCU;
end function;



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


function SupercuspidalRamified(F, K, f, c, VarepsGenerators)
    p := Prime(F);
    print("p="),p;
    if p eq 2 then
        return SupercuspidalRamified2(F, K, f, c, VarepsGenerators);
    elif p eq 3 then
        return SupercuspidalRamified3(F, K, f, c, VarepsGenerators);
    else
        error Error("Prime must be 2 or 3");
    end if;
end function;

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
            Values := Values cat [0 : i in [1 .. #Uf1*(1 + #GalEGens)]];

            time for mu in GalEGens do
                muUf1:=[proj(Norm(mu(g),K1)): g in UpStairsUf];
                Elements := Elements cat [Uf1[i] - muUf1[i] : i in [1 .. #Uf1]];
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
    - A list of lists, each with Supercuspidal Ramified Types of the twist #i
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

    PS := PrincipalSeries(F, ff : MyComplex := [*groups, maps, lift*]);
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
            SCR_K := SupercuspidalRamified(F, K, f, c, VarepsGenerators);
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
                vprintf ECITypes: "Computed %o exceptional types of size 24 for cubic extension #%o\n", &+[#c : c in Ex_L], j;
            end for;
            L := FieldOfFractions(AllExtensions(F,3)[4]);
            Ex8 := ExceptionalTypesTriply(F,L);
            vprintf ECITypes: "Computed %o exceptional types of size 8\n", &+[#c : c in Ex8];
        else 
            Ex24 := ExceptionalTypesSimply(F);
            vprintf ECITypes: "Computed %o exceptional types of size 24\n", &+[#c : c in Ex24];
        end if;
    end if;

    return Twist, PS, SCU, SCR, Ex8, Ex24;
end intrinsic;