AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q3 := pAdicField(3, 100);
Q9 := UnramifiedExtension(Q3, 2);

time PS, SCU, SCR, Ex8, Ex24, Twist := InertialTypes(Q9);

InTypesSummary(PS,SCU,SCR,Ex8,Ex24);
