load "Complexes3.m";
load "Characters.m";
load "Utils.m";

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
            NewPrincipalSeriesIT(phi) 
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
            NewSupercuspidalUnramifiedIT(phi, F)
            : phi in FastCharactersOfOrder(groups[1], n, maps, lift)
        ];
    end for;

    return SCU;
end function;


function VarepsilonFilter(VarepsGenerators, minus_one, chi, lift)
    for bar_g in VarepsGenerators do
        // bar_g := Inverse(lift)(g);
        if not (chi(bar_g) eq Codomain(chi)!minus_one) then
            return false;
        end if;
    end for;
    return true;
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
        NewSupercuspidalRamifiedIT(phi, F)
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
        NewSupercuspidalRamifiedIT(phi, F)
        : phi in FastCharactersOfOrder(groups[1], 6, maps, lift : Elements:=VarepsGenerators, Values:=Values)
    ];
end function;


function SupercuspidalRamified(F, K, f, c, VarepsGenerators)
    p := Prime(F);
    if p eq 2 then
        return SupercuspidalRamified2(F, K, f, c, VarepsGenerators);
    elif p eq 3 then
        return SupercuspidalRamified3(F, K, f, c, VarepsGenerators);
    else
        error Error("Prime must be 2 or 3");
    end if;
end function;


Q2 := pAdicField(2,1000);
Q4 := UnramifiedExtension(Q2, 2);
K := FieldOfFractions(AllExtensions(Q2, 2)[1]);

Q3 := pAdicField(3,1000);
Q9 := UnramifiedExtension(Q3, 2);