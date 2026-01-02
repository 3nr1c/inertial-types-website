load "Main.m";
load "EllipticCurves.m";




function CompareType(E, Twist, PS, SCU, SCR, Ex8, Ex24,AllCurves)
    if Valuation(jInvariant(E)) gt 0 then 
        E;
        #PS;
        #SCU;
        [#SCR[i]: i in [1..#SCR]];
        [#Ex24[i]: i in [1..#Ex24]];
        #Ex8;
        tau := InTypeOf(E, Twist, PS, SCU, SCR, Ex8, Ex24);
        if Type(tau) eq RngIntElt then return tau, PS, SCU, SCR, Ex8, Ex24, AllCurves; end if;

        if Type(tau) eq  PrincipalSeriesIT then
            for j in [1..#PS] do
                if tau eq PS[j] then 
                    PS:=Remove(PS,j);
                    AllCurves[1]:=Append(AllCurves[1],[*E,tau*]);
                    break;
                end if; 
            end for; 
        elif Type(tau) eq SupercuspidalUnramifiedIT then
            for j in [1..#SCU] do
                if tau eq SCU[j] then 
                    SCU:=Remove(SCU,j);
                    AllCurves[2]:=Append(AllCurves[2],[*E,tau*]);
                    break;
                end if; 
            end for;

        elif Type(tau) eq SupercuspidalRamifiedIT then
            for i in [1..#SCR] do
                for j in [1..#SCR[i]] do
                    if tau eq SCR[i,j] then 
                        SCR[i]:=Remove(SCR[i],j); 
                        AllCurves[3]:=Append(AllCurves[3],[*E,tau*]);
                        break;
                    end if;
                end for;
            end for;
        elif Type(tau) eq ExceptionalIT then
            if IsRamified(tau`CubicField) then    
                for i in [1..#Ex24] do
                    for j in [1..#Ex24[i]] do
                        if tau eq Ex24[i,j] then 
                            Ex24[i]:=Remove(Ex24[i],j);
                            AllCurves[5]:=Append(AllCurves[5],[*E,tau*]);
                            break;
                        end if; 
                    end for;
                end for;
            else
                for j in [1..#Ex8] do             
                    if tau eq Ex8[j] then 
                        Ex8:=Remove(Ex8,j);
                        AllCurves[4]:=Append(AllCurves[4],[*E,tau*]);
                        break;
                    end if; 
                end for;
            end if;
        end if;
    end if;
    return tau, PS, SCU, SCR, Ex8, Ex24, AllCurves;
end function;


/*
Extensions, Twists := AllQuadraticExtensions(Q2);
F := Extensions[1];

Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(F);
p, ram_deg, in_deg, pi, N := BaseValues(F);
u := 1 + pi;

PSCurves:=[* *];
PSTypes:=[* *];
SCUCurves:=[* *];
SCUTypes:=[* *];
SCRCurves:=[* *];
SCRTypes:=[* *];
Ex24Curves:=[* *];
Ex24Types:=[* *];
Ex8Curves:=[* *];
Ex8Types:=[* *];



AllCurves:=[*[* *],[* *],[* *],[* *],[* *]*];
for a, b, c, d, e, f in [0..3] do  
    if ((#PS eq 0) and (#SCU eq 0) and  [#SCR[i] : i in [1..#SCR]] eq [0 : j in [1..#SCR]] and [#Ex24[i] : i in [1..#Ex24]] eq [0 : j in [1..#Ex24]]) then break; end if;
        a,b,c,d,e,f;
        a2 := pi^a * u^d;
        a4 := pi^b * u^e;
        a6 := pi^c * u^f;

        isEC, E := IsEllipticCurve([F!0,a2,0,a4,a6]);
        if not isEC then continue; end if;
        if Valuation(jInvariant(E)) gt 0 then 
            tau, PS, SCU, SCR, Ex8, Ex24,AllCurves:=CompareType(E, Twist, PS, SCU, SCR, Ex8, Ex24, AllCurves);
            if not Type(tau) eq RngIntElt then
                for t in Twist do
                    E1:=QuadraticTwist(E,t);
                    tau, PS, SCU, SCR, Ex8, Ex24, AllCurves:=CompareType(E1, Twist, PS, SCU, SCR, Ex8, Ex24, AllCurves);
                end for;
            end if;
        end if;
end for;
*/

    