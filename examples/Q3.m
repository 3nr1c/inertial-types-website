AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q2 := pAdicField(3, 100);

time Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(Q2);

PrintInChtrSummary(PS,SCU,SCR,Ex8,Ex24);