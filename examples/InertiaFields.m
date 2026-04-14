AttachSpec("../spec");
AttachSpec("../../padic_db/spec");

SetVerbose("InTypes", true);
SetVerbose("InFields", 1);

Qp := pAdicField(3, 100);
i := 5; i;
F := FieldOfFractions(AllExtensions(Qp,3)[i]);
// F := SplittingField(quadratics[i]); 
// F := Qp;
F;
MinimalPolynomial(F.1);

// BE CAREFUL WITH THE FILENAME TO AVOID OVERWRITING PRECOMPUTED DATA
// FILENAME := Sprintf("../data/out_smallpolys_Q3_L%o.m", i);
FILENAME := Sprintf("../data/out_smallpolys_Q%o_%o_K%o.m",Prime(F),Degree(F,Qp),i);
FILENAME;

time PS, SCU, SCR, _, _, Twist := InTypes(F : SkipExceptionals:=true, InFields:=true);
InTypesSummary(PS,SCU,SCR);

PrintFile(FILENAME, "Twist := ");
PrintFileMagma(FILENAME, Twist);
PrintFile(FILENAME, ";");

PrintFile(FILENAME, "data := [*");
for tau in PS do
    inertia := InField(tau);
    inertia := SplittingField(BetterPoly(DefiningPolynomial(inertia), inertia, BaseField(inertia)));
    relpoly := DefiningPolynomial(Integers(inertia), Integers(F));
    relpoly := BetterPoly(relpoly, inertia, F);
    try
        time polyF := PolRedPadic(relpoly, Integers(F));
        "Used PolRedPadic";
    catch e
        polyF := relpoly;
        "Used BetterPoly";
    end try;
    polyF;
    PrintFileMagma(FILENAME,  [*
        "principal series", SemistabilityDefect(tau), tau`CondExp, tau`Character`Order, polyF
    *]);
    PrintFile(FILENAME, ",");
end for;

for tau in SCU do
    inertia := InField(tau);
    inertia := SplittingField(BetterPoly(DefiningPolynomial(inertia), inertia, BaseField(inertia)));
    relpoly := DefiningPolynomial(Integers(inertia), Integers(F));
    relpoly := BetterPoly(relpoly, inertia, F);
    try
        time polyF := PolRedPadic(relpoly, Integers(F));
        "Used PolRedPadic";
    catch e
        polyF := relpoly;
        "Used BetterPoly";
    end try;
    polyF;
    PrintFileMagma(FILENAME,  [*
        "supercuspidal unramified", SemistabilityDefect(tau), tau`CondExp, tau`Character`Order, polyF
    *]);
    PrintFile(FILENAME, ",");
end for;

for tau in SCR do
    inertia := InField(tau);
    inertia := SplittingField(BetterPoly(DefiningPolynomial(inertia), inertia, BaseField(inertia)));
    relpoly := DefiningPolynomial(Integers(inertia), Integers(F));relpoly;
    relpoly := BetterPoly(relpoly, inertia, F);
    try
        time polyF := PolRedPadic(relpoly, Integers(F));
        "Used PolRedPadic";
    catch e
        polyF := relpoly;
        "Used BetterPoly";
    end try;
    polyF;
    PrintFileMagma(FILENAME,  [*
        "supercuspidal ramified", SemistabilityDefect(tau), tau`CondExp, tau`Character`Order, polyF, 
        DefiningPolynomial(tau`Character`Field, F)
    *]);
    PrintFile(FILENAME, ",");
end for;

if Prime(F) eq 2 then
    time Ex8, Ex24 := ExceptionalTypes(F : InFields := true);
    InTypesSummary(PS,SCU,SCR,Ex8,Ex24);

    for tau in Ex8 do
        inertia := InField(tau);
        //inertia := SplittingField(BetterPoly(DefiningPolynomial(inertia), inertia, BaseField(inertia)));
        relpoly := DefiningPolynomial(Integers(inertia), Integers(F));
        relpoly;
        relpoly := BetterPoly(relpoly, inertia, F, tau : minprec:=10);
        try
            time polyF := PolRedPadic(relpoly, Integers(F));
            "Used PolRedPadic";
        catch e
            polyF := relpoly;
            "Used BetterPoly";
        end try;
        polyF;
        PrintFileMagma(FILENAME,  [*
            "exceptional Q8", SemistabilityDefect(tau), tau`CondExp, tau`Character`Order, polyF,
            DefiningPolynomial(tau`TriplyField, F), DefiningPolynomial(tau`Character`Field, tau`TriplyField)
        *]);
        PrintFile(FILENAME, ",");
    end for;

    queue := [1..#Ex24];
    while #queue gt 0 do
        i := queue[1];
        tau := Ex24[i];

        inertia := InField(tau);
        //inertia := SplittingField(BetterPoly(DefiningPolynomial(inertia), inertia, BaseField(inertia)));
        time relpoly := DefiningPolynomial(Integers(inertia), Integers(F));
        time relpoly := BetterPoly(relpoly, inertia, F, tau: minprec:=10);
        relpoly;
        try
            time polyF := PolRedPadic(relpoly, Integers(F));
            polyF; 
            "Used PolRedPadic";
        catch e
            polyF := relpoly;
            "Used BetterPoly";
        end try;
        PrintFileMagma(FILENAME,  [*
            "exceptional SL(2,3)", SemistabilityDefect(tau), tau`CondExp, tau`Character`Order, polyF,
            DefiningPolynomial(tau`TriplyField, F), DefiningPolynomial(tau`Character`Field, tau`TriplyField)
        *]);
        PrintFile(FILENAME, ",");
        Remove(~queue, 1);
    end while;
    PrintFile(FILENAME, "*];");
else
    PrintFile(FILENAME, "*];");
end if;