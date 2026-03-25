AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q2 := pAdicField(2, 100);

time PS, SCU, SCR, Ex8, Ex24, Twist := InertialTypes(Q2 : InertiaFields := true);

InTypesSummary(PS,SCU,SCR,Ex8,Ex24);