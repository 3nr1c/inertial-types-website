AttachSpec("../spec");

SetVerbose("InTypes", true);
SetVerbose("InFields", 1);

Q2 := pAdicField(2, 100);
Q16 := UnramifiedExtension(Q2, 4);

time PS, SCU, SCR, Ex8, Ex24, Twist := InTypes(Q16 : SkipExceptionals:=true, InFields:=true);

InTypesSummary(PS,SCU,SCR,Ex8,Ex24);
