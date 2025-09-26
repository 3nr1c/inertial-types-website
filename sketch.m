
function CharactersOfOrder(G, n)
    Zn := AdditiveGroup(Integers(n));
    GZn, t := Hom(G, Zn);
    return {t(f) : f in GZn | Order(f) eq n};
end function;


function CharacterFactorsThrough(A, B, pi, chi)
    Zn := Codomain(chi);
    for g in Generators(Kernel(pi)) do
        if chi(g) ne Zn!0 then
            return false;
        end if;
    end for;
    return true;
end function;

A := UnitGroup(Integers(36));
B := UnitGroup(Integers(12));
AB, t := Hom(A,B);
pi := t(AB.1);
for chi in CharactersOfOrder(A, 2) do
   if CharacterFactorsThrough(A, B, pi, chi) then
     print(chi);
   end if;
end for;