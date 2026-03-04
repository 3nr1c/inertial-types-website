AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q2 := pAdicField(2, 100);
K1 := FieldOfFractions(AllExtensions(Q2, 2)[1]);

time Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(K1);