AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q2 := pAdicField(2, 100);
Q4 := UnramifiedExtension(Q2, 2);

time PS, SCU, SCR, Ex8, Ex24, Twist := InertialTypes(Q4 : InertiaFields:=false);

InTypesSummary(PS,SCU,SCR,Ex8,Ex24);
