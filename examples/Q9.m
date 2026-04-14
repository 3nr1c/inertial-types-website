AttachSpec("../spec");

SetVerbose("InTypes", 2);
SetVerbose("InFields", 2);

Q3 := pAdicField(3, 100);
Q9 := UnramifiedExtension(Q3, 2);

time PS, SCU, SCR, Ex8, Ex24, Twist := InTypes(Q9 : InFields:=false);

InTypesSummary(PS,SCU,SCR,Ex8,Ex24);
