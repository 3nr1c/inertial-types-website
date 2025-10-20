load "Complexes3.m";
load "Characters.m";
load "Postprocessing.m";

function ComputeChars(order, instantiation, filters)
    groups, maps, lift := instantiation();
    Chars := CharactersOfOrder(groups[1], order);
    for filter in filters do
        Chars := [chi : chi in Chars | filter(chi, lift)];
    end for;
    return AddConductor(Chars, groups, maps, order);
end function;

function PrincipalSeries(F, f : MyComplex:=[* *])
    if #MyComplex eq 3 then
        groups := MyComplex[1];
        maps := MyComplex[2];
        lift := MyComplex[3];
    else
        groups, maps, lift := UComplex(F, f);
    end if;
    instantiation := func< | groups, maps, lift>;
    AllChars := [* *];
    for n in {2, 3, 4, 6} do
        AllChars cat:= ComputeChars(n, instantiation, [func< x, ... | true >]);
    end for;

    return AllChars;
end function;


function SupercuspidalUnramified(F, K, f)
    if Valuation(Discriminant(K,F)) gt 0 then
        error Error("The extension K|F is not unramified");
    end if;

    groups, maps, lift := ConComplex(F, K, f);
    instantiation := func< | groups, maps, lift>;
    AllChars := [* *];
    for n in {3, 4, 6} do
        AllChars cat:= ComputeChars(n, instantiation, [func< chi, ... | true >]);
    end for;

    return AllChars;
end function;


function VarepsilonFilter(VarepsGenerators, minus_one, chi, lift)
    for g in VarepsGenerators do
        bar_g := Inverse(lift)(g);
        if not IsIdentity(bar_g) and not (chi(bar_g) eq Codomain(chi)!minus_one) then
            return false;
        end if;
    end for;
    return true;
end function;


function SupercuspidalRamified2(F, K, f, c, VarepsGenerators)
    assert Prime(F) eq 2;

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    Cond, pi, Gal, y := ExtValues(F, K);
    if (in_deg mod 2) eq 0 then
        // (in_deg mod 2) eq 0 checks if x^2+x+1 splits in F
        // Triply imprimitive with n = 4, characters must be quadratic on y
        quadratic_filter := func< chi, lift | IsIdentity(2 * chi(Inverse(lift)(y)))>;
    else
        // Simply imprimitive with n = 4, characters must *not* be quadratic on y
        quadratic_filter := func< chi, lift | not IsIdentity(2 * chi(Inverse(lift)(y)))>;
    end if;
    return ComputeChars(4, func< | ConComplex(F, K, f)>, 
    [
        quadratic_filter,   
        func< chi, lift | VarepsilonFilter(VarepsGenerators, 2, chi, lift)>
    ]);
end function;

function SupercuspidalRamified3(F, K, f, c, VarepsGenerators)
    assert Prime(F) eq 3;
    return ComputeChars(6, func< | ConComplex(F, K, f)>, 
        func< chi, lift | VarepsilonFilter(VarepsGenerators, 3, chi, lift)>);
end function;

function SupercuspidalRamified2args(F, K)
    p, ram_deg, in_deg, pi, N := BaseValues(F);
    Cond, pi, Gal, y := ExtValues(F,K);
    f := Max(N-Cond, 2*Cond);
    c := Cond;

    UGroups, UMaps, ULift := UComplex(F, f);
    G := UGroups[f - c + 1];
    if f - c + 1 eq 1 then
        llift := ULift;
    else
        llift := Inverse(UMaps[f - c]) * ULift;
    end if;
    VarepsGenerators := {K!llift(g) : g in Generators(G)};

    if p eq 2 then
        return SupercuspidalRamified2(F, K, f, c, VarepsGenerators);
    elif p eq 3 then
        return SupercuspidalRamified3(F, K, f, c, VarepsGenerators);
    else
        error Error("Prime must be 2 or 3");
    end if;
end function;

function SupercuspidalRamified2withoutArgs(F, K)
    assert Prime(F) eq 2;

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    f, c, VarepsGenerators := GetVarepsilonGenerators(F, K);
    Cond, pi, Gal, y := ExtValues(F,K);

    if (in_deg mod 2) eq 0 then
        // (in_deg mod 2) eq 0 checks if x^2+x+1 splits in F
        // Triply imprimitive with n = 4, characters must be quadratic on y
        quadratic_filter := func< chi, lift | IsIdentity(2 * chi(Inverse(lift)(y)))>;
    else
        // Simply imprimitive with n = 4, characters must *not* be quadratic on y
        quadratic_filter := func< chi, lift | not IsIdentity(2 * chi(Inverse(lift)(y)))>;
    end if;
    CGroups, CMaps, CLift := ConComplex(F, K, f);
    // CGroups[1];
    return ComputeChars(4, func< | CGroups, CMaps, CLift >, 
                [
                    quadratic_filter,
                    func< chi, lift | VarepsilonFilter(VarepsGenerators, 2, chi, lift)>
                ]), 
        CGroups, CMaps, CLift;
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

function InertialTypes(F) 
    c := 0;
    QuadExt := [FieldOfFractions(Z) : Z in AllExtensions(F, 2)];

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    ff := Floor(N/2);
    printf "f=%o\n", ff;
    groups, maps, lift := UComplex(F, ff);
    #groups;

    chars := PrincipalSeries(F, ff : MyComplex := [*groups, maps, lift*]);
    #chars;
    // [[*char[2],char[3]*] : char in chars];
    print("----");

    i := 1;
    for K in QuadExt do
        i;
        Cond, pi, Gal, y := ExtValues(F,K);
        c := Cond;
        if Cond eq 0 then
            chars := SupercuspidalUnramified(F,K,ff);
            #chars;
            // [[*char[2],char[3]*] : char in chars];
        else 
            f := Max(N-Cond, 2*Cond);
            printf "f=%o\n", f;
            printf "c=%o\n", c;
            G := groups[ff - c + 1];
            if ff - c + 1 eq 1 then
                llift := lift;
            else
                llift := Inverse(maps[ff - c]) * lift;
            end if;
            VarepsGenerators := {K!llift(g) : g in Generators(G)};
            chars := SupercuspidalRamified(F, K, f, c, VarepsGenerators);
            printf "%o characters\n", #chars;
            // [[*char[2],char[3]*] : char in chars];
            print("----");
        end if;
        i +:= 1;
    end for;

    return 0;
end function;

Q2 := pAdicField(2,100);
Q4 := UnramifiedExtension(Q2, 2);
K := FieldOfFractions(AllExtensions(Q2, 2)[1]);