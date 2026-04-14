AttachSpec("../spec");

SetVerbose("InTypes", true);

Q2 := pAdicField(2, 100);
CubeExt := AllExtensions(Q2,3);
for i in [1..#CubeExt] do
    i;
    K := FieldOfFractions(CubeExt[i]);
    K;
    time PS, SCU, SCR, Ex8, Ex24, Twist := InertialTypes(K);
    InTypesSummary(PS,SCU,SCR,Ex8,Ex24);
end for;