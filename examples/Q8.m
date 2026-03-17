AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q2 := pAdicField(2, 100);
Q8 := UnramifiedExtension(Q2, 3);

time  Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(Q8 : SkipExceptionals := true);

PrintInChtrSummary(PS,SCU,SCR,Ex8,Ex24);
