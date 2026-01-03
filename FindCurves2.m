Attach("ECGenerator.spec");
// load "Main.m";
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


// F:=FieldOfFractions(AllExtensions(Q2,2)[2]);
// Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(F);
FTwist:=FundamentalTwist(Twist);
AllCurves:=AssociativeArray();
AllCurves["PS"] := AssociativeArray();
AllCurves["SCU"] := AssociativeArray();
AllCurves["SCR"] := AssociativeArray();
AllCurves["Ex24"] := AssociativeArray();
AllCurves["Ex8"] := AssociativeArray();

PSc  := AssociativeArray();
for tau in PS do
    if not (tau`CondExp in Keys(PSc)) then
        PSc[tau`CondExp] := [tau];
        AllCurves["PS",tau`CondExp] := [* *];
    else
        Append(~PSc[tau`CondExp], tau);
    end if;
end for;

SCUc  := AssociativeArray();
for tau in SCU do
    if not (tau`CondExp in Keys(SCUc)) then
        SCUc[tau`CondExp] := [tau];
        AllCurves["SCU",tau`CondExp] := [* *];
    else
        Append(~SCUc[tau`CondExp], tau);
    end if;
end for;

SCRc := [];
for i in [1..#SCR] do
    Append(~SCRc, AssociativeArray());
    for tau in SCR[i] do
        if not (tau`CondExp in Keys(SCRc[i])) then
            SCRc[i,tau`CondExp] := [tau];
            AllCurves["SCR",[i,tau`CondExp]]:=[* *];
        else
            Append(~SCRc[i,tau`CondExp], tau);
        end if;
    end for;
end for;

Ex8c  := AssociativeArray();
for tau in Ex8 do
    CondExp:=tau`Character`CondExp+Valuation(Discriminant(tau`Character`Field,tau`CubicField));
    if not (CondExp in Keys(Ex8c)) then
        Ex8c[CondExp] := [tau];
        AllCurves["Ex8",CondExp]:=[* *];
    else
        Append(~Ex8c[CondExp], tau);
    end if;
end for;

Ex24c := [];
for i in [1..#Ex24] do
    Append(~Ex24c, AssociativeArray());
    for tau in Ex24[i] do
        if not (tau`CondExp in Keys(Ex24c[i])) then
            Ex24c[i,tau`CondExp] := [tau];
            AllCurves["Ex24",[i,tau`CondExp]]:=[* *]; 
        else
            Append(~Ex24c[i,tau`CondExp], tau);
        end if;
    end for;
end for;



function FindPS(F,PSc,AllCurves,FTwist)
    FTwist := [1] cat FTwist;

    ECGenerator := EllipticCurveGenerator(F : InitialBase := 5, method := 2);
    while &or [#c gt 0 : c in PSc] do
        E := Next(ECGenerator);

        CondExp := Valuation(Conductor(E));
        if not CondExp in Keys(PSc) or IsEmpty(PSc[CondExp]) then continue; end if;

        L := mTorsionField(E,3);
        if  (RamificationDegree(L,F) ge 8) then 
            continue; 
        elif (not IsAbelian(L,F)) then 
            continue; 
        else
            follow := false; i := 1;
            repeat 
                E1 := QuadraticTwist(E,FTwist[i]);
                CondExp1 := Valuation(Conductor(E1));
                i +:= 1;

                if not CondExp1 in Keys(PSc) or IsEmpty(PSc[CondExp1]) then continue; end if;

                L := i eq 1 select L else mTorsionField(E1,3);
                tau := FindInertiaType(L, PSc[CondExp1]);
                    
                if IsNull(tau) then continue; end if;

                Exclude(~PSc[CondExp1], tau);
                Append(~AllCurves["PS",CondExp1],[*E1,tau*]);
                follow := true;
                tau;
            until not (follow and i le #FTwist);
        end if;
    end while;
    return AllCurves;
end function;

function FindSCU(F,SCUc,AllCurves,FTwist)

    ECGenerator := EllipticCurveGenerator(F : InitialBase := 2, method := 2);
    i := 0;
    while &or [#c gt 0 : c in SCUc] do
        E := Next(ECGenerator);

        CondExp := Valuation(Conductor(E));
        if not CondExp in Keys(SCUc) or IsEmpty(SCUc[CondExp]) then continue; end if;

        L := mTorsionField(E,3);
        if (RamificationDegree(L,F) ge 8) then 
            continue; 
        elif IsAbelian(L,F) then 
            continue; 
        else
            EK := BaseChange(E,SCUc[CondExp][1]`Character`Field);
            L := mTorsionField(EK,3);
            tau := FindInertiaType(L, SCUc[CondExp]);

            if IsNull(tau) then continue; end if;

            Exclude(~SCUc[CondExp], tau);
            Append(~AllCurves["SCU",CondExp], [*E,tau*]);
            tau;
            i+:=1;i;
            
            for t in FTwist do
                E1 := QuadraticTwist(E,t);
                CondExp1 := Valuation(Conductor(E1));

                if not CondExp1 in Keys(SCUc) or IsEmpty(SCUc[CondExp1]) then continue; end if;

                EK1 := BaseChange(E1,SCUc[CondExp1][1]`Character`Field);
                L := mTorsionField(EK1,3);
                tau := FindInertiaType(L, SCUc[CondExp1]);

                if IsNull(tau) then continue; end if;
                
                Exclude(~SCUc[CondExp1], tau);
                Append(~AllCurves["SCU", CondExp1], [*E1,tau*]);
                tau;
                i+:=1;i;
            end for;
        end if;
    end while;
    return AllCurves;
end function;

function FindSCR(F,SCRc,AllCurves,Twist,FTwist)
    p, ram_deg, in_deg, pi, N := BaseValues(F);

    for i in [1..#SCRc] do  
        ECGenerator := EllipticCurveGenerator(F : InitialBase := 4);
        if IsEmpty(Keys(SCRc[i])) then continue; end if;
        while &or [#c gt 0 : c in SCRc[i]] do
            E := Next(ECGenerator);

            CondExp:=Valuation(Conductor(E));
            if not CondExp in Keys(SCRc[i]) or IsEmpty(SCRc[i,CondExp]) then continue; end if;

            L:=mTorsionField(E,3);
            if not (RamificationDegree(L,F) eq 8) then 
                continue; 
            elif (in_deg mod 2 eq 0) and Degree(L,F) ge 24 then 
                continue; 
            elif (IsSquare(L!Twist[i])) and (Valuation(Conductor(BaseChange(QuadraticTwist(E,Twist[i]),L))) eq 0) then

                EK := BaseChange(E,SCRc[i,CondExp,1]`Character`Field);
                L := mTorsionField(EK,3);
                tau := FindInertiaType(L, SCRc[i,CondExp]);

                if IsNull(tau) then continue; end if;

                Exclude(~SCRc[i,CondExp],tau);
                Append(~AllCurves["SCR",[i,CondExp]],[*E,tau*]);
                tau;

                for t in FTwist do
                    E1 := QuadraticTwist(E,t);
                    CondExp1 := Valuation(Conductor(E1));
                    
                    if not CondExp1 in Keys(SCRc[i]) or IsEmpty(SCRc[i,CondExp1]) then continue; end if;

                    EK1 := BaseChange(E1,SCRc[i,CondExp1,1]`Character`Field);
                    L := mTorsionField(EK1,3);
                    tau := FindInertiaType(L, SCRc[i,CondExp1]);

                    if IsNull(tau) then continue; end if;

                    Exclude(~SCRc[i,CondExp1],tau);
                    Append(~AllCurves["SCR",[i,CondExp1]],[*E1,tau*]);
                    tau;
                end for;
            end if;
        end while;
    end for;

    return AllCurves;
end function;

function FindEx24(F, Ex24c, AllCurves, Twist, FTwist)
    p, ram_deg, in_deg, pi, N := BaseValues(F);

    for i in [1..#Ex24c] do
        if #Keys(Ex24c[i]) eq 0 then continue; end if;
        for c in Ex24c[i] do
            CubicField := c[1]`CubicField;
            K := c[1]`Character`Field;
            Poly := DefiningPolynomial(K, CubicField);
            break;
        end for;
        Poly;
        Keys(Ex24c[i]);

        ECGenerator := EllipticCurveGenerator(F : InitialBase := 5, method := 2);
        while &or [#c gt 0 : c in Ex24c[i]] do
            E := Next(ECGenerator);

            CondExp := Valuation(Conductor(E));
            if not CondExp in Keys(Ex24c[i]) or IsEmpty(Ex24c[i,CondExp]) then continue; end if;

            L:=mTorsionField(E,3);
            d := Degree(L,F);
            if (in_deg mod 2 eq 0) and d lt 24 then
                continue;
            elif (in_deg mod 2 eq 1) and d lt 48 then
                continue; 
            else
                L := mTorsionField(BaseChange(E,CubicField), 3);
                if Degree(L, CubicField)*Degree(CubicField, F) ne d then continue; end if;

                Lx<x>:=PolynomialRing(L);

                hasRoot := HasRoot(Lx!Poly);

                if hasRoot then 
                    E1 := BaseChange(E, K);
                    time L1 := mTorsionField(E1, 3);
                    time tau := FindInertiaType(L1, Ex24c[i, CondExp]);
                    print("------------------------");
                    Exclude(~Ex24c[i,CondExp], tau);
                    Append(~AllCurves["Ex24",[i,CondExp]], [*E, tau*]);
                    tau;
                    #Ex24c[i,CondExp];

                    for t in FTwist do
                        E1 := QuadraticTwist(E,t);
                        CondExp1 := Valuation(Conductor(E1));
                        
                        if not CondExp1 in Keys(Ex24c[i]) or IsEmpty(Ex24c[i,CondExp1]) then continue; end if;

                        EK1 := BaseChange(E1, K);
                        time L1 := mTorsionField(EK1,3);
                        time tau := FindInertiaType(L1, Ex24c[i,CondExp1]);

                        if IsNull(tau) then continue; end if;

                        print("------------------------");
                        Exclude(~Ex24c[i,CondExp1], tau);
                        Append(~AllCurves["Ex24",[i,CondExp1]], [*E1, tau*]);
                        tau;
                        #Ex24c[i,CondExp1];
                    end for;
                    // if Type(char) eq RngIntElt then continue; end if;
                    // chi:=char;
                else
                    print("Poly has no root");
                end if;

            end if;
        end while;
    end for;

    return AllCurves;
end function;
