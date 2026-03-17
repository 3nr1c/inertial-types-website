AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q2 := pAdicField(2, 100);
QuadExt := AllExtensions(Q2,2);
for i in [1..#QuadExt] do
    i;
    K := FieldOfFractions(QuadExt[i]);
    K;
    time Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(K);
    PrintInChtrSummary(PS,SCU,SCR,Ex8,Ex24);
end for;