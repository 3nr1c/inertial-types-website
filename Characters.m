function CharactersOfOrder(G, n)
    Zn := AdditiveGroup(Integers(n));
    GZn, t := Hom(G, Zn);
    GZn_half := {};
    for f in GZn do
        if not (-f in GZn_half) and Order(f) eq n then
            Include(~GZn_half, f);
        end if;
    end for;
    return {t(f) : f in GZn_half};
end function;


function CharacterFactorsThrough(A, B, pi, chi)
    for g in Generators(Kernel(pi)) do
        if not IsIdentity(chi(g)) then
            return false;
        end if;
    end for;
    return true;
end function;

function ListValueFilter(list, val, chi, lift)
    for g in list do
        Inverse(lift)(g);
        if not (chi(Inverse(lift)(g)) eq Codomain(chi)!val) then return false; end if;
    end for;
    return true;
end function;

function ComputeConductor(chi, groups, maps)
    f := #groups;
    cond := f;
    while cond gt 1 and  \
        CharacterFactorsThrough(groups[1], groups[f - cond + 2], maps[f - cond + 1], chi) do
        cond := cond - 1;
    end while;
    return cond;
end function;