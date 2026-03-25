AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q2 := pAdicField(2, 40);
Q2x<x> := PolynomialRing(Q2);
// > [DefiningPolynomial(FieldOfFractions(O)) : O in AllExtensions(Q2,2)];
quadratics := [
    x^2 + 2*x + 2,
    x^2 + 2*x + 3*2,
    x^2 + 2,
    x^2 + 5*2,
    x^2 + 3*2,
    x^2 + 7*2,
    x^2 + x + 1
];
i := 2; i;
F := UnramifiedExtension(Q2,3);
//F := ChangePrecision(SplittingField(quadratics[i]),40); 
F;
MinimalPolynomial(F.1);

time PS, SCU, SCR, Ex8, Ex24, Twist := InertialTypes(F : SkipExceptionals:=false, InertiaFields:=true);

InTypesSummary(PS,SCU,SCR,Ex8,Ex24);

SetVerbose("ECITypes", false);
// SetVerbose("ClassField", 5);

printf "[\n";
for tau in PS do
    inertia := InertiaField(tau);
    poly := DefiningPolynomial(inertia, Q2);
    relpoly := DefiningPolynomial(inertia, F);
    R := Parent(poly);
    S := Parent(relpoly);
    AssignNames(~R, ["X"]);
    AssignNames(~S, ["T"]);
    printf "\t[* \"principal series\", %o, %o, %o, %o *],\n", SemistabilityDefect(tau), tau`CondExp, tau`Character`Order, relpoly;
end for;

for tau in SCU do
    inertia := InertiaField(tau);
    poly := DefiningPolynomial(inertia, Q2);
    relpoly := DefiningPolynomial(inertia, F);
    R := Parent(poly);
    S := Parent(relpoly);
    AssignNames(~R, ["X"]);
    AssignNames(~S, ["T"]);
    printf "\t[* \"supercuspidal unramified\", %o, %o, %o, %o *],\n", SemistabilityDefect(tau), tau`CondExp, tau`Character`Order, relpoly;
end for;

for tau in SCR do
    inertia := InertiaField(tau);
    poly := DefiningPolynomial(inertia, Q2);
    relpoly := DefiningPolynomial(inertia, F);
    R := Parent(poly);
    S := Parent(relpoly);
    AssignNames(~R, ["X"]);
    AssignNames(~S, ["T"]);
    printf "\t[* \"supercuspidal ramified\", %o, %o, %o, %o *],\n", SemistabilityDefect(tau), tau`CondExp, tau`Character`Order, relpoly;
end for;

for tau in Ex8 do
    inertia := InertiaField(tau);
    poly := DefiningPolynomial(inertia, Q2);
    relpoly := DefiningPolynomial(inertia, F);
    R := Parent(poly);
    S := Parent(relpoly);
    AssignNames(~R, ["X"]);
    AssignNames(~S, ["T"]);
    printf "\t[* \"exceptional Q8\", %o, %o, %o, %o *],\n", SemistabilityDefect(tau), tau`CondExp, tau`Character`Order, relpoly;
end for;

for tau in Ex24 do
    inertia := InertiaField(tau);
    poly := DefiningPolynomial(inertia, Q2);
    relpoly := DefiningPolynomial(inertia, F);
    R := Parent(poly);
    S := Parent(relpoly);
    AssignNames(~R, ["X"]);
    AssignNames(~S, ["T"]);
    printf "\t[* \"exceptional SL(2,3)\", %o, %o, %o, %o *],\n", SemistabilityDefect(tau), tau`CondExp, tau`Character`Order, relpoly;
end for;
printf "]\n";