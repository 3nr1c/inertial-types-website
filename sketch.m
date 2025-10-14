load "Complexes.magma";
load "CharacterUtils.m";



// An example: find the conductor of the characters of order 4

F := UnramifiedExtension(pAdicField(2,100),2);
K := FieldOfFractions(AllExtensions(F,2)[1]);
f := 6; // This will change according to the situation
c := 4;

Cond,pi,Gal,y := ExtValues(F,K);
L := Varepsilon(F,K,f,c);

UGroups, UMaps, ULift , Uf:= UComplex(K,f);
Groups, Maps, CLift:= ConComplex(UGroups,UMaps,ULift,Uf);
Project := Inverse(CLift);
// CLift(Groups[1].1);
// Maps[4](Maps[3](Maps[2](Maps[1](Groups[1].2))));
// Maps[2](Groups[2].1);

G := Groups[1];
gens := Generators(G);
f;G;gens;
y_unlift := Project(y);
AllChars := {chi : chi in CharactersOfOrder(G, 4) | IsIdentity(2 * chi(y_unlift))};
for l in L do
    l_unlift := Project(l);
    AllChars := {chi : chi in AllChars | chi(l_unlift) eq Codomain(chi)!2};
end for;
#AllChars;

for chi in AllChars do
    chi_cond := f;
    G := Groups[1];
    while chi_cond gt 1 and  \
        CharacterFactorsThrough(G, Groups[f - chi_cond + 2], Maps[f - chi_cond + 1], chi) do
        chi_cond := chi_cond - 1;
    end while;
    print(chi(gens));
    print(chi_cond);
    print("");
end for;

/* ********************** */

// Old test:
// A := UnitGroup(Integers(36));
// B := UnitGroup(Integers(12));
// AB, t := Hom(A,B);
// pi := t(AB.1);
// for chi in CharactersOfOrder(A, 2) do
//    if CharacterFactorsThrough(A, B, pi, chi) then
//      print(chi);
//    end if;
// end for;
