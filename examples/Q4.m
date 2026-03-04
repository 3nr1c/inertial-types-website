AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q2 := pAdicField(2, 100);
Q4 := UnramifiedExtension(Q2, 2);

time Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(Q4);