load "Complexes.magma";
load "Characters.m";
load "Postprocessing.m";

function ComputeChars(order, instantiation, filters)
    groups, maps, lift := instantiation();
    Chars := CharactersOfOrder(groups[1], order);
    for filter in filters do
        Chars := [chi : chi in Chars | filter(chi, lift)];
        // Chars;
    end for;
    return AddConductor(Chars, groups, maps);
end function;

function PrincipalSeriesOfOrder(F, f, n)
    return ComputeChars(n, func< | UComplex(F, f)>, [func< x, ... | true >]);
end function;

function SupercuspidalUnramifiedOfOrder(F, K, f,  n)
    assert n in {3, 4, 6};
    if Valuation(Discriminant(K,F)) gt 0 then
        error Error("The extension K|F is not unramified");
    end if;

    minus_one := n eq 4 select 2 else 3;
    return ComputeChars(n, func< | ConComplex(F, K, f)>, 
        [func< chi, lift | true >]);
end function;

function SupercuspidalRamified2(F, K, f, c)
    assert Prime(F) eq 2;

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    NonNormGenerators := Varepsilon(F, K, f, c);
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
        func< chi, lift | ListValueFilter(NonNormGenerators, 2, chi, lift)>
    ]);
end function;

function SupercuspidalRamified3(F, K, f, c)
    assert Prime(F) eq 3;
    NonNormGenerators := Varepsilon(F, K, f, c);
    return ComputeChars(6, func< | ConComplex(F, K, f)>, 
        func< chi, lift | ListValueFilter(NonNormGenerators, 3, chi, lift)>);
end function;

function SupercuspidalRamified(F, K, f, c)
    p := Prime(F);
    if p eq 2 then
        return SupercuspidalRamified2(F, K, f, c);
    elif p eq 3 then
        return SupercuspidalRamified3(F, K, f, c);
    else
        error Error("Prime must be 2 or 3");
    end if;
end function;


function InertialTypes(F) 
    c := 0;
    QuadExt := [];
    for Z in AllExtensions(F, 2) do
        K := FieldOfFractions(Z);
        QuadExt := Append(QuadExt,K);
        m := Valuation(Discriminant(K,F));
        c := Max(m,c);
    end for;

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    f := Floor(N/2);
    for n in [2,3,4,6] do
        chars := PrincipalSeriesOfOrder(F,f,n);
        printf("Principal series of order: ");print(n);
        #chars;
        [char[2] : char in chars];
        print("----");
    end for;

    i := 1;
    for K in QuadExt do
        Cond, pi, Gal, y := ExtValues(F,K);
        f := Max(N-Cond, 2*Cond);
        c := Cond;
        // print(f);print(c);
        if Cond gt 0 then
            i;
            chars := SupercuspidalRamified(F,K,f,c);
            #chars;
            [char[2] : char in chars];
            print("----");
        else 
            for n in [3,4,6] do
                chars := SupercuspidalUnramifiedOfOrder(F,K,f,n);
                print(n);
                #chars;
                [char[2] : char in chars];
                print("----");
            end for;
        end if;
        i +:= 1;
    end for;
    return 0;
end function;

Q2 := pAdicField(2, 100);
Q4 := UnramifiedExtension(Q2, 2);