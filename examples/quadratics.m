AttachSpec("../spec");

SetVerbose("InTypes", true);
SetVerbose("InFields", 1);

Q2 := pAdicField(2, 100);
QuadExt := AllExtensions(Q2,2);
PS := [];
SCU := [];
SCR := [];
Ex8 := [];
Ex24 := [];
Twist := [];
for i in [1..#QuadExt] do
    i;
    K := FieldOfFractions(QuadExt[i]);
    K;
    time PSi, SCUi, SCRi, Ex8i, Ex24i, Twisti := InTypes(K : InFields:=true, SkipExceptionals:=true);
    Append(~PS, PSi);
    Append(~SCU, SCUi);
    Append(~SCR, SCRi);
    Append(~Ex8, Ex8i);
    Append(~Ex24, Ex24i);
    InTypesSummary(PS[i], SCU[i], SCR[i], Ex8[i], Ex24[i]);
end for;