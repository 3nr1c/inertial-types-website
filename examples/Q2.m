AttachSpec("../spec");

SetVerbose("InTypes", 2);
SetVerbose("InFields", 2);

Q2 := pAdicField(2, 100);

time PS, SCU, SCR, Ex8, Ex24, Twist := InTypes(Q2 : InFields := true);

InTypesSummary(PS,SCU,SCR,Ex8,Ex24);

tau := Ex24[1];
N := InField(tau);
poly := DefiningPolynomial(N, Q2);
BetterPoly(poly, N, Q2, tau);
