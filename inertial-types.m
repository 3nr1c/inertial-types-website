load "Complexes.magma";
load "Characters.m";

function PrincipalSeriesOfOrder(F, f, n)
    UGroups, UMaps, ULift := UComplex(F, f);
    UProj := Inverse(ULift);

    assert #UGroups eq f;
    assert #UMaps eq f-1;

    G := UGroups[1];
    Gens := Generators(G);
    Chars := CharactersOfOrder(G, n);

    Output := [* *];

    for chi in Chars do
        chi_cond := f;
        while chi_cond gt 1 and  \
            CharacterFactorsThrough(G, UGroups[f - chi_cond + 2], UMaps[f - chi_cond + 1], chi) do
            chi_cond := chi_cond - 1;
        end while;
        Append(~Output, [* chi, chi_cond, chi(Gens) *]);
    end for;

    return ULift(Gens), Output;
end function;

function InternalSupercuspidalOfOrder(F, K, f, c, n)
    assert n in {3, 4, 6};

    // UGroups, UMaps, ULift := UComplex(K, f);
    // Uf := ComputeUf(F, K, f);
    // CGroups, CMaps, CLift := ConComplex(UGroups, UMaps, ULift, Uf);
    CGroups, CMaps, CLift := ConComplex(F, K, f);
    CProject := Inverse(CLift);
    
    assert #CGroups eq f;
    assert #CMaps eq f-1;

    G := CGroups[1];
    #G;
    Gens := Generators(G);
    Chars := CharactersOfOrder(G, n);

    // 
    p, ram_deg, in_deg, pi, N := BaseValues(F);
    Cond, pi, Gal, y := ExtValues(F, K);
    bar_y := CProject(y);

    // Sieving
    if Cond gt 0 then 
        // K|F ramified
        print("K|F ramified");
        if p eq 2 then
            assert n eq 4;
            if (in_deg mod 2) eq 0 then
                // (in_deg mod 2) eq 0 checks if x^2+x+1 splits in F
                // Triply imprimitive with n = 4, characters must be quadratic on y
                print("Characters will induce a triply imprimitive type.");
                Chars := {chi : chi in CharactersOfOrder(G, 4) | IsIdentity(2 * chi(bar_y))};
            else
                // Simply imprimitive with n = 4, characters must *not* be quadratic on y
                print("Characters will induce a simply imprimitive type.");
                Chars := {chi : chi in CharactersOfOrder(G, 4) | not IsIdentity(2 * chi(bar_y))};
            end if;
        elif p eq 3 then
            assert n eq 6;
            print("Characters will induce a simply imprimitive type.");
            Chars := CharactersOfOrder(G, 6);
        else
            error Error("There is no supercuspidal ramified type for p > 3");
        end if;
    else
        // SupercuspidalUnramified
        // n is 3, 4 or 6
        print("K|F Unramified");
        Chars := CharactersOfOrder(G, n);
    end if;

    NonNormGenerators := Varepsilon(F, K, f, c);
    assert IsEmpty(NonNormGenerators) or not (n eq 3);
    minus_one := n eq 4 select 2 else 3;
    for g in NonNormGenerators do
        bar_g := CProject(g);
        Chars := {chi : chi in Chars | chi(bar_g) eq Codomain(chi)!minus_one};
    end for;

    Output := [* *];

    for chi in Chars do
        chi_cond := f;
        while chi_cond gt 1 and  \
            CharacterFactorsThrough(G, CGroups[f - chi_cond + 2], CMaps[f - chi_cond + 1], chi) do
            chi_cond := chi_cond - 1;
        end while;
        Append(~Output, [* chi, chi_cond, chi(Gens) *]);
    end for;

    return CLift(Gens), Output;
end function;

function SupercuspidalUnramifiedOfOrder(F, K, f, c, n)
    return InternalSupercuspidalOfOrder(F, K, f, c, n);
end function;

function SupercuspidalRamified(F, K, f, c)
    p := Prime(F);
    if p eq 2 then
        n := 4;
    elif p eq 3 then
        n := 6;
    else
        error Error("There is no supercuspidal ramified type for p > 3");
    end if;

    return InternalSupercuspidalOfOrder(F, K, f, c, n);
end function;

function InertialTypes(F) 
    c:=0;
    QuadExt:=[];
    for Z in AllExtensions(F,2) do
        K:=FieldOfFractions(Z);
        QuadExt:=Append(QuadExt,K);
        m:=Valuation(Discriminant(K,F));
        c:=Max(m,c);
    end for;

    p,ram_deg,in_deg,pi,N:=BaseValues(F);
    f:=Floor(N/2);
    for n in [2,3,4,6] do
        gens, chars := PrincipalSeriesOfOrder(F,f,n);
        printf("Principal series of order: ");print(n);
        #chars;
        [char[2] : char in chars];
        print("----");
    end for;

    for K in QuadExt do
        Cond,pi,Gal,y:=ExtValues(F,K);
        f:=N-Cond;
        print(f);print(c);
        if Cond gt 0 then
            gens, chars := SupercuspidalRamified(F,K,f,c);
            #chars;
            [char[2] : char in chars];
            print("----");
        else 
            for n in [3,4,6] do
                gens, chars := InternalSupercuspidalOfOrder(F,K,f,c,n);
                print(n);
                #chars;
                [char[2] : char in chars];
                print("----");
            end for;
        end if;
    end for;
    return 0;
end function;

