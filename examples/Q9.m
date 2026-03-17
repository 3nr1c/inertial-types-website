AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q3 := pAdicField(3, 100);
Q9 := UnramifiedExtension(Q3, 2);

time Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(Q9);

PrintInChtrSummary(PS,SCU,SCR,Ex8,Ex24);
