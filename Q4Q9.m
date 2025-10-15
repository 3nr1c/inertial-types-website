load "inertial-types2.m";

Q2 := pAdicField(2, 100);
Q4 := UnramifiedExtension(Q2, 3);

for Z in AllExtensions(Q4,2) do
    K := FieldOfFractions(Z);
    chars := SupercuspidalRamified(Q4,K,6,3);
    #chars;
    [c[2] : c in chars];
    print("----");
end for; 

// Q3 := pAdicField(3, 100);
// Q9 := UnramifiedExtension(Q3, 2);

// for Z in AllExtensions(Q9,2) do
//     K := FieldOfFractions(Z);
//     gens, chars := InternalSupercuspidalOfOrder(Q9,K,6,4,6);
//     #chars;
//     [c[2] : c in chars];
//     print("----");
// end for; 