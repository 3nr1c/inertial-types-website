AttachSpec("../spec");

SetVerbose("InTypes", true);

Q3 := pAdicField(3, 100);

time PS, SCU, SCR, Ex8, Ex24, Twist := InTypes(Q3);

InTypesSummary(PS,SCU,SCR,Ex8,Ex24);