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

function SupercuspidalUnramifiedOfOrder(F, K, f, c, n)
    // Varepsilon condition
    return 0;
end function;

function SimplyImprimitiveOfOrder(F, K, f, c, n)
    // Varepsilon condition
    // Uniformizer conditions
    return 0;

end function;

function TriplyImprimitiveOfOrder(F, K, f, c, n)
    // Varepsilon condition
    // Uniformizer conditions: quadratic char on u/sigma(u)
    return 0;

end function;