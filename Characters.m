function CharactersOfOrder(G, n)
    /* Todo: modulo inverses */
    Zn := AdditiveGroup(Integers(n));
    GZn, t := Hom(G, Zn);
    GZn_half := [];
    for t in GZn do
        if not (-t in GZn_half) then
            Append(~GZn_half, t);
        end if;
    end for;
    return {t(f) : f in GZn_half | Order(f) eq n};
end function;


function CharacterFactorsThrough(A, B, pi, chi)
    for g in Generators(Kernel(pi)) do
        if not IsIdentity(chi(g)) then
            return false;
        end if;
    end for;
    return true;
end function;