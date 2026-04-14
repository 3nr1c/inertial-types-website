AttachSpec("../spec");

SetVerbose("InTypes", 1);
SetVerbose("InFields", 1);

Q2 := pAdicField(2, 200);
Q4 := UnramifiedExtension(Q2, 2);

time PS, SCU, SCR, Ex8, Ex24, Twist := InTypes(Q4 : InFields:=false, SkipExceptionals:=true);

InTypesSummary(PS,SCU,SCR,Ex8,Ex24);
