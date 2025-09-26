
function CharactersOfOrder(G, n)
    Zn := AdditiveGroup(Integers(n));
    GZn, t := Hom(G, Zn);
    return {t(f) : f in GZn | Order(f) eq n};
end function;


function CharacterFactorsThrough(A, B, pi, chi)

end function;

A := UnitGroup(Integers(36));
B := UnitGroup(Integers(12));
// pi := reduction map
// for chi in CharactersOfOrder(A, 4) do
//    if CharacterFactorsThrough(A, B, pi, chi) then
//      print(chi);
//    end if;
// end for;