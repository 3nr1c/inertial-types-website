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


F:=FieldOfFractions(AllExtensions(Q2,2)[2]);
Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(F);
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

SCRc  := AssociativeArray();
for i in [1..#SCR] do
    SCRc[i]:=AssociativeArray();
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

Ex24c  := AssociativeArray();
for i in [1..#Ex24] do
    for tau in Ex24[i] do
        CondExp:=tau`Character`CondExp+Valuation(Discriminant(tau`Character`Field,tau`CubicField));
        if not ([i,CondExp] in Keys(Ex24c)) then
            Ex24c[[i,CondExp]] := [tau];
            AllCurves["Ex24",[i,CondExp]]:=[* *]; 
        else
            Append(~Ex24c[[i,CondExp]], tau);
        end if;
    end for;
end for;




//OF:=ChangePrecision(Integers(F),AbsoluteRamificationDegree(F)+1);
//UF:=UnitGroup(OF);
//Gen:=Generators(UF);
//u:=[a: a in Gen][1];

function FindPS(F,PSc,AllCurves,FTwist)
p, ram_deg, in_deg, pi, N := BaseValues(F);
u := 1 + pi;

for i,j,k in [1,0] do
    for a, b, c, d, e, f in [0..3] do  
        if &and [IsEmpty(c) : c in PSc] then return AllCurves; end if;
        i,j,k,a,b,c,d,e,f;
        a2 := i*pi^d * u^a;
        a4 := j*pi^e * u^b;
        a6 := k*pi^f * u^c;
        isEC, E := IsEllipticCurve([F!0,a2,0,a4,a6]);
        if not isEC then continue; end if;
        if (Valuation(jInvariant(E)) gt 0) then 
            CondExp:=Valuation(Conductor(E));
            if not CondExp in Keys(PSc) or IsEmpty(PSc[CondExp]) then continue; end if;
                L:=mTorsionField(E,3);
            if  (RamificationDegree(L,F) ge 8) then 
                continue; 
            elif (not IsAbelian(L,F)) then 
                    continue; 
            else
                tau:=FindInertiaType(L, PSc[CondExp]);
                if not Type(tau) eq RngIntElt then
                    PSc[CondExp]:=Remove(PSc[CondExp],Index(PSc[CondExp],tau));
                    Append(~AllCurves["PS",CondExp],[*E,tau*]);
                    AllCurves;
                    for t in FTwist do
                        E1:=QuadraticTwist(E,t);
                        CondExp1:=Valuation(Conductor(E1));
                        if not CondExp1 in Keys(PSc) or IsEmpty(PSc[CondExp1]) then continue; end if;
                        L:=mTorsionField(E1,3);
                        tau:=FindInertiaType(L, PSc[CondExp1]);
                        if not Type(tau) eq RngIntElt then
                        PSc[CondExp1]:=Remove(PSc[CondExp1],Index(PSc[CondExp1],tau));
                        Append(~AllCurves["PS",CondExp1],[*E1,tau*]);
                        end if;
                    end for;
                end if;
            end if;
        end if;
    end for;
end for;

return AllCurves;
end function;

function FindSCU(F,SCUc,AllCurves,FTwist)
p, ram_deg, in_deg, pi, N := BaseValues(F);
u := 1 + pi;

for i,j,k in [1,0] do
    for a, b, c, d, e, f in [0..3] do  
        if &and [IsEmpty(c) : c in SCUc] then return AllCurves; end if;
        i,j,k,a,b,c,d,e,f;
        a2 := i*pi^d * u^a;
        a4 := j*pi^e * u^b;
        a6 := k*pi^f * u^c;
        isEC, E := IsEllipticCurve([F!0,a2,0,a4,a6]);
        if not isEC then continue; end if;
        if (Valuation(jInvariant(E)) gt 0) then 
            CondExp:=Valuation(Conductor(E));
            if not CondExp in Keys(SCUc) or IsEmpty(SCUc[CondExp]) then continue; end if;
                L:=mTorsionField(E,3);
            if  (RamificationDegree(L,F) ge 8) then 
                continue; 
            elif IsAbelian(L,F) then 
                    continue; 
            else
                EK:=BaseChange(E,SCUc[CondExp][1]`Character`Field);
                L:= mTorsionField(EK,3);
                tau:=FindInertiaType(L, SCUc[CondExp]);
                if not Type(tau) eq RngIntElt then
                    SCUc[CondExp]:=Remove(SCUc[CondExp],Index(SCUc[CondExp],tau));
                    Append(~AllCurves["SCU",CondExp],[*E,tau*]);
                    AllCurves;
                    for t in FTwist do
                        E1:=QuadraticTwist(E,t);
                        CondExp1:=Valuation(Conductor(E1));
                        if not CondExp1 in Keys(SCUc) or IsEmpty(SCUc[CondExp1]) then continue; end if;
                        EK1:=BaseChange(E1,SCUc[CondExp1][1]`Character`Field);
                        L:= mTorsionField(EK1,3);
                        tau:=FindInertiaType(L, SCUc[CondExp1]);
                        if not Type(tau) eq RngIntElt then
                        SCUc[CondExp1]:=Remove(SCUc[CondExp1],Index(SCUc[CondExp1],tau));
                        Append(~AllCurves["SCU",CondExp1],[*E1,tau*]);
                        end if;
                    end for;
                end if;
            end if;
        end if;
    end for;
end for;

return AllCurves;
end function;

function FindSCR(F,SCRc,AllCurves,Twist,FTwist)
p, ram_deg, in_deg, pi, N := BaseValues(F);
u := 1 + pi;
Fx<x>:=PolynomialRing(F);

for f in Keys(SCRc) do
    if IsEmpty(Keys(SCRc[f])) then continue; end if;
    for i,j,k in [1,0] do
        if &and [IsEmpty(c) : c in SCRc[f]] then break; end if;
        for a, b, c, d, e, g in [0..3] do  
            if &and [IsEmpty(c) : c in SCRc[f]] then break; end if;
            i,j,k,a,b,c,d,e,g;
            a2 := i*pi^d * u^a;
            a4 := j*pi^e * u^b;
            a6 := k*pi^g * u^c;
            isEC, E := IsEllipticCurve([F!0,a2,0,a4,a6]);
            if not isEC then continue; end if;
            if (Valuation(jInvariant(E)) gt 0) then 
                CondExp:=Valuation(Conductor(E));
                if not CondExp in Keys(SCRc[f]) or IsEmpty(SCRc[f,CondExp]) then continue; end if;
                    L:=mTorsionField(E,3);
                if not (RamificationDegree(L,F) eq 8) then 
                    continue; 
                elif (in_deg mod 2 eq 0) and Degree(L,F) ge 24 then 
                    continue; 
                elif (IsSquare(L!Twist[f])) and (Valuation(Conductor(BaseChange(QuadraticTwist(E,Twist[f]),L))) eq 0) then
                    EK:=BaseChange(E,SCRc[f,CondExp][1]`Character`Field);
                    L:= mTorsionField(EK,3);
                    tau:=FindInertiaType(L, SCRc[f,CondExp]);
                    if not Type(tau) eq RngIntElt then
                        SCRc[f,CondExp]:=Exclude(SCRc[f,CondExp],tau);
                        Append(~AllCurves["SCR",[f,CondExp]],[*E,tau*]);
                        AllCurves;
                        for t in FTwist do
                            E1:=QuadraticTwist(E,t);
                            CondExp1:=Valuation(Conductor(E1));
                            if not CondExp1 in Keys(SCRc[f]) or IsEmpty(SCRc[f,CondExp1]) then continue; end if;
                            EK1:=BaseChange(E1,SCRc[f,CondExp1][1]`Character`Field);
                            L:= mTorsionField(EK1,3);
                            tau:=FindInertiaType(L, SCRc[f,CondExp1]);
                            if not Type(tau) eq RngIntElt then
                            SCRc[f,CondExp1]:=Exclude(SCRc[f,CondExp1],tau);
                            Append(~AllCurves["SCR",[f,CondExp1]],[*E1,tau*]);
                            end if;
                        end for;
                    end if;
                end if;
            end if;
        end for;
    end for;
end for;

return AllCurves;
end function;












































//PSCurves:=[* *];
//PSTypes:=[* *];
//SCUCurves:=[* *];
//SCUTypes:=[* *];
//SCRCurves:=[* *];
//SCRTypes:=[* *];
//Ex24Curves:=[* *];
//Ex24Types:=[* *];
//Ex8Curves:=[* *];
//Ex8Types:=[* *];
/*
AllCurves:=[*[* *],[* *],[* *],[* *],[* *]*];



for i,j,k in [0,1] do
    for a, b, c, d, e, f in [0..3] do  
        if (#PS eq 0) and (#SCU eq 0) and  ([#SCR[i] : i in [1..#SCR]] eq [0 : j in [1..#SCR]]) then break; end if;
            a,b,c,d,e,f;
            a2 := i*pi^a * u^d;
            a4 := j*pi^b * u^e;
            a6 := k*pi^c * u^f;

            isEC, E := IsEllipticCurve([F!0,a2,0,a4,a6]);
            if not isEC then continue; end if;
            if Valuation(jInvariant(E)) gt 0 then 
                L:=mTorsionField(E,3);
                if Degree(L,F) eq 48 then continue;
                else
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

ExceptionalFields:=[* *];
ExceptionalCurves:=[* *];
function CompareReduction(E,Fields)
for L in Fields do
    if Valuation(Conductor(BaseChange(E,L))) eq 0 then return false; end if;
end for;
return true;
end function;

for a, b, c, d, e, f in [0..3] do  
    if (#PS eq 0) and (#SCU eq 0) and  ([#SCR[i] : i in [1..#SCR]] eq [0 : j in [1..#SCR]]) then break; end if;
        a,b,c,d,e,f;
        a2 := pi^a * u^d;
        a4 := pi^b * u^e;
        a6 := pi^c * u^f;

        isEC, E := IsEllipticCurve([F!0,a2,0,a4,a6]);
        if not isEC then continue; end if;
        if Valuation(jInvariant(E)) gt 0 then 
            L:=mTorsionField(E,3);
            if not (Degree(L,F) eq 48) then continue;
            else
                if CompareReduction(E,ExceptionalFields) then
                    ExceptionalCurves:=Append(ExceptionalCurves,E);
                    ExceptionalFields:=Append(ExceptionalFields,L);
                    for t in FundamentalTwist do
                        E1:=QuadraticTwist(E,t);
                        if CompareReduction(E1,ExceptionalFields) then
                            ExceptionalCurves:=Append(ExceptionalCurves,E1);
                            ExceptionalFields:=Append(ExceptionalFields,mTorsionField(E1,3));
                        end if;
                    end for;
                end if;
            end if;
        end if;
        #ExceptionalCurves;
end for;
*/