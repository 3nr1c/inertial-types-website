import "utils.m" : FastMap;

function BaseValues(F)
    Z := Integers();
    p := Prime(F);
    e := AbsoluteRamificationDegree(F);
    f := AbsoluteInertiaDegree(F);
    pi := UniformizingElement(F);
    N := Z!(6*Valuation(F!2)+3*Valuation(F!3)+2);
    return p,e,f,pi,N;
end function;

function ExtValues(F,K)
    pi := UniformizingElement(K);
    Cond := Valuation(Discriminant(K,F));
    Gal := Automorphisms(K,F);
    y := pi/Gal[2](pi);
    return Cond,pi,Gal,y;
end function;


// This function compute Ugroups for higher values of f
function UComplex(K, f)
    p,e,fK,pi,N := BaseValues(K);
    Groups := [];
    UMaps := [* *];

    K1 := ChangePrecision(K,f);
    OK1 := Integers(K1);
    FqBasis := Basis(ResidueClassField(OK1));
    UK1,mK1 := UnitGroup(OK1);
    ULift := mK1*Coercion(OK1,K1)*Coercion(K1,K);
    Groups := Append(Groups,UK1);
    UProj := Inverse(ULift);

    for i in [1..f-1] do
        L := [];
        for x in FqBasis do
            z:=ChangePrecision(K!K1!OK1!x,Precision(K));
            if IsEmpty(UMaps) then L:=Append(L,UProj(1+z*pi^(f-i))); else L:=Append(L,UMaps[i-1](UProj(1+z*pi^(f-i)))); end if;
        end for;

        G,phi:=quo<Groups[i]|L>;
        Groups:=Append(Groups,G);
        if IsEmpty(UMaps) then UMaps:=Append(UMaps,FastMap(phi)); else UMaps:=Append(UMaps,FastMap(UMaps[i-1]*phi)); end if;
        end for;

    return Groups,UMaps,ULift;
end function;

function ConComplex(F, K, f)
    // This seems to be the slowest function (might want to do some timings)
    assert f gt AbsoluteRamificationDegree(K);
    UGroups, UMaps,ULift := UComplex(K, f);
    // Factorization(#UGroups[1]);

    // #UGroups;
    UK1 := UGroups[1];
    UProj := Inverse(ULift);
    Uf := sub<UK1|[UProj(K!Norm(ChangePrecision(ULift(g),Precision(K)), F)) : g in Generators(UK1)]>;

    CGroups := [];
    CMaps := [* *];
    G,pr := quo<UGroups[1]|Uf>;
    CLift := Inverse(pr)*ULift;
    CGroups := Append(CGroups,G);
    // Factorization(#G);

    for i in [1..f-1] do
        G,phi := quo<UGroups[i+1]|UMaps[i](Uf)>;
        CGroups := Append(CGroups,G);
        CMaps := Append(CMaps,FastMap(Inverse(pr)*UMaps[i]*phi));
    end for;

    return CGroups, CMaps, CLift;
end function;

function GetVarepsilonGenerators(F, K : MyComplex := [* *])
    p, ram_deg, in_deg, pi, N := BaseValues(F);
    Cond, pi, Gal, y := ExtValues(F,K);
    f := Max(N-Cond, 2*Cond);
    c := Cond;

    if #MyComplex eq 3 then
        UGroups := MyComplex[1];
        UMaps := MyComplex[2];
        ULift := MyComplex[3];
    else
        UGroups, UMaps, ULift := UComplex(F, f);
    end if;
    ff := #UGroups;
    ff;c;
    G := UGroups[ff - c + 1];
    if ff - c + 1 eq 1 then
        llift := ULift;
    else
        llift := Inverse(UMaps[ff - c]) * ULift;
    end if;
    VarepsGenerators := {K!llift(g) : g in Generators(G)};

    return f, c, VarepsGenerators;
end function;

// function FastMap(A,B,m)
//     Fmap:=hom<A->B|[m(A.j) : j in [1..#Generators(A)]]>;
//     return Fmap;
// end function;
