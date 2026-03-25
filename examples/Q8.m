AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q2 := pAdicField(2, 100);
Q8 := UnramifiedExtension(Q2, 3);

time  PS, SCU, SCR, Ex8, Ex24, Twist := InertialTypes(Q8 : SkipExceptionals := true);

InTypesSummary(PS,SCU,SCR,Ex8,Ex24);
