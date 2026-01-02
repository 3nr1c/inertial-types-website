u:=1+pi;
for i,j,k in [0,1] do 
    for a,b,c, d, e,f in [0..6] do  
        if (#PS eq 0) and (#SCU eq 0) and  ([#SCR[i] : i in [1..#SCR]] eq [0 : j in [1..#SCR]]) then break; end if;
            a,b,c,d,e,f,i,j,k;
            //a1 := pi^l * u^e;
            //a3 := pi^k * u^d;
            a2 := k*pi^f * u^c;
            a4 := j*pi^e * u^b;
            a6 := i*pi^d * u^a;

            isEC, E := IsEllipticCurve([0,F!a2,0,a4,a6]);
            if not isEC then continue; end if;
            if (Valuation(jInvariant(E)) gt 0) and ((Valuation(Conductor(E))) eq 14) then
                print("----------------------------------"); 
                L:=mTorsionField(E,3);
                    if (IsAbelian(L,F)) then
                        tau, PS, SCU, SCR, Ex8, Ex24,AllCurves:=CompareType(E, Twist, PS, SCU, SCR, Ex8, Ex24, AllCurves);
                        if not Type(tau) eq RngIntElt then
                            for t in FTwist do
                                E1:=QuadraticTwist(E,t);
                                tau, PS, SCU, SCR, Ex8, Ex24, AllCurves:=CompareType(E1, Twist, PS, SCU, SCR, Ex8, Ex24, AllCurves);
                            end for;
                        end if;
                    end if;
            end if;
    end for;
end for;