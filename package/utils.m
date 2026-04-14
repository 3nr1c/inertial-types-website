function AllQuadraticExtensions(F : Selmer:=true)
    Extensions := [];
    Twist:=[];
    if Selmer then
        R<x> := PolynomialRing(F);
        Sel,FtoSel := pSelmerGroup(2,F);
        SeltoF := Inverse(FtoSel);

        for s in Sel do
            if IsIdentity(s) then continue; end if;
            z:=ChangePrecision(SeltoF(s), Precision(F));
            Append(~Extensions, SplittingField(x^2 - z));
            Append(~Twist, z);
        end for;
    else
        for Z in AllExtensions(F, 2) do
            Append(~Extensions, FieldOfFractions(Z));
            Append(~Twist, Discriminant(FieldOfFractions(Z), F));
        end for;
    end if;

    return Extensions, Twist;
end function;

function FundamentalTwist(Twist)
    test:=[];
    FTwist:=[];
    F:=Parent(Twist[1]);
    R<x> := PolynomialRing(F);
    Sel,FtoSel := pSelmerGroup(2,F);
    SeltoF := Inverse(FtoSel);
    for t in Twist do
        if RamificationDegree(SplittingField(x^2-t),F) eq 1 then sun:=FtoSel(t); end if;
    end for;

    for t in Twist do
    s:=FtoSel(t);
    if (not s eq sun) and (not s in test) and (not s*sun in test) then test:=Append(test,s); FTwist:=Append(FTwist,t); end if;  
    end for;

    return FTwist;
end function;

function FastMap(m)
// Given two groups A,B and a map m define as a composite
// of different maps it returns the map that goes directly from A to B without 
// passing thorough all the composites.
    A := Domain(m);
    B := Codomain(m);
    Gens := [g : g in Generators(A)];
    Fmap := Homomorphism(A, B, Gens, [m(g) : g in Gens]);
    return Fmap;
end function;

function OptimalNorms(L,F,f : prec:=0)
// resulting precision is >= prec
    r := RamificationDegree(L,F);
    c := Max([r*(f-1)+1,AbsoluteRamificationDegree(L)+1,prec]);
    
    assert Ceiling(c/r) ge f;

    LowPrecL := ChangePrecision(L,c);
    OL := Integers(LowPrecL);
    // Using UnitGroupGenerators instead of UnitGroup saves _a lot_ of time
    GenUL := UnitGroupGenerators(OL);
    UL, ULtoOL := UnitGroup(OL);
    // GenUL := SetToSequence(Generators(UL));

    upstairs := [ChangePrecision(L!LowPrecL!g,Precision(L)) :g in GenUL];
    // upstairs := [ChangePrecision(L!LowPrecL!ULtoOL(g),Precision(L)) :g in GenUL];

    return
        [ChangePrecision(Norm(u, F),Precision(F)) : u in upstairs],
        upstairs, UL, ULtoOL;
end function;

function ElementCoordinates(x, B);
//'''Returns the coordinates of x in the basis B'''
    L := Parent(B[1]);
    assert Degree(L) eq #B;//: "Provided vectors are not a basis";
    basis:=[];
    for b in B do
        Append(~basis,ElementToSequence(b));
    end for;
    P_1 := Matrix(basis);
    assert Determinant(P_1) ne 0;//: "Provided vectors are not a basis";
    P := Matrix(basis)^(-1);
    K := BaseRing(P);

    xs := Vector(ElementToSequence(L!x));
    xsP := xs * P;
    return [xsP[i] : i in [1..#B]];
end function;

function CharInertiaField(chi)
    K:=chi`Field;
    Cond:=chi`CondExp;
    ChiLift:=chi`Lift;
    K2:=ChangePrecision(K,Max([10,Cond,AbsoluteRamificationDegree(K)+4]));
    U,m:=UnitGroup(K2);
    Utors:=sub<U|[g : g in Generators(U)| not IsZero(Order(g))]>;
    f:=Coercion(Utors,U)*m*Coercion(K2,K)*Inverse(ChiLift)*chi`Map;
    f:=FastMap(f);
    Norms,mN:=sub<U|Kernel(f),Inverse(m)(UniformizingElement(K2))>;
    L:=ClassField(m,Norms);
    return L,U/Norms;
end function;



function IsValidExceptionalExtension(F, L)
    if (AbsoluteInertiaDegree(F) mod 2 eq 0) then
        valid := (Degree(L, F) eq 3);
        if not valid then
            vprintf InTypes : "L/F must be a cubic extension";
        end if;
    else //(AbsoluteInertiaDegree(F) mod 2 eq 1)
        if Degree(L, F) ne 6 then
            vprintf InTypes : "L/F must be an extension of degree 6";
        end if;
        if not IsNormal(L, F) then
            vprintf InTypes : "L/F must be normal";
        end if;
        if InertiaDegree(L, F) ne 2 then
            vprintf InTypes : "L/F must have inertia degree 2";
        end if;
        valid := (Degree(L, F)) eq 6 and (IsNormal(L, F)) and (InertiaDegree(L, F) eq 2);
    end if;

    return valid;
end function;

function CmpCondExp(tau1, tau2)
    return tau1`CondExp - tau2`CondExp;
end function;

intrinsic BetterPoly(p::., L::FldPad, K::FldPad : minprec := 10, SkipHasRoot:=false) -> .
{}
    Kx := Parent(p);
    pseq := ElementToSequence(p);
    for prec in [minprec..Precision(K)] do
        betterp := Kx![ChangePrecision(ChangePrecision(c, prec), Precision(K)) : c in pseq];

        time irred := IsIrreducible(betterp);
        if irred then
            if SkipHasRoot then break; end if;
            time hasroot := HasRoot(betterp, L);
            if hasroot then 
                break;
            end if;
        end if;
    end for;
    return betterp;
end intrinsic;

intrinsic BetterPoly(p::., N::FldPad, F::FldPad, tau::ExceptionalInType : minprec := 10) -> .
{}
    Fx := Parent(p);
    pseq := ElementToSequence(p);
    L := tau`TriplyField;
    M := BaseField(N);
    pK1 := DefiningPolynomial(tau`Triply`InducingFields[1], L);// basis 1, y1 over L
    pK2 := DefiningPolynomial(tau`Triply`InducingFields[2], L);// basis 1, y2 over K1
    discN := ElementToSequence(Discriminant(N, M));
    _, y2 := HasRoot(pK2, M);
    discN := ElementCoordinates(discN, [1, y2]);// coordinates in basis 1, y2
    D := ElementToSequence(discN[1]) cat ElementToSequence(discN[2]);// coordinates in basis 1,y1,y2,y1*y2
    for prec in [minprec..Precision(F)] do
        betterp := Fx![ChangePrecision(ChangePrecision(c, prec), Precision(F)) : c in pseq];

        try
            time irred := IsIrreducible(betterp);
            if irred then
                time N2 := FieldOfFractions(SplittingField(ChangeRing(betterp, L) : Std:=false));
                // Degree(N2,F);
                // N2;
                if Degree(N2, F) ne Degree(p) then continue; end if;
                hasRoot1, r1 := HasRoot(pK1, N2);
                hasRoot2, r2 := HasRoot(pK2, N2);
                // hasRoot1, hasRoot2;
                if not hasRoot1 or not hasRoot2 then continue; end if;

                discN_N2 := D[1] + D[2]*r1 + D[3]*r2 + D[4]*r1*r2;
                // IsSquare(discN_N2);
                if IsSquare(discN_N2) then break; end if;
            end if;
        catch e
            print(e);
            continue;
        end try;
    end for;
    return betterp;
end intrinsic;

intrinsic BetterPoly(L::FldPad, K::FldPad : minprec := 10) -> .
{}
    time p := DefiningPolynomial(L, K);
    return BetterPoly(p, L, K);
end intrinsic;