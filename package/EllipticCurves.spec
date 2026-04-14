import "sequences.m" : BaseValues;


declare type CrvEllGenerator;
declare attributes CrvEllGenerator:
    F,
    pi,
    u,
    InitialBase,
    Base,
    counter,
    ijk,
    curve,
    method
;

intrinsic EllipticCurveGenerator(F::FldPad : InitialBase := 4, method := 2) -> CrvEllGenerator 
{Create an object that yields elliptic curves over F with potentially good reduction}
    ECG := New(CrvEllGenerator);
    ECG`F := F;
    pi := UniformizingElement(F);
    ECG`pi := pi;
    OF:=Integers(F);
    if Degree(F) eq 2 then
        for x1,x2 in [0..10] do
            z:=F![x1,x2];
            if IsUnit(OF!z) and not (z in BaseRing(F)) then z; ECG`u := z; break x1;  end if;
        end for;
    else
        G, m := UnitGroup(OF);
        for x in Generators(G) do
        // for x1,x2 in [0..10] do
            // z:=F![x1,x2];
            z := m(x);
            ECG`u := z;
            z;break;
        end for;
    end if;
    ECG`Base := InitialBase;
    ECG`InitialBase := ECG`Base;
    ECG`ijk := 1;
    ECG`counter := -1;
    ECG`method := method;
    return ECG;
end intrinsic;

// function NextMethod1(G)
// end function;

intrinsic Next(G::CrvEllGenerator) -> CrvEll
{Return a new elliptic curve according to the internal state of the generator}
    found := false;
    repeat
        G`counter +:= 1;
        if G`counter gt (G`Base^6 - 1) then
            G`ijk +:= 1;
            G`counter := 0;
            if G`ijk gt 7 then
                G`ijk := 1;
                G`Base +:= 1;
            end if;
        end if;

        abcdef := Reverse(IntegerToSequence(G`counter, G`Base));
        if G`Base eq G`InitialBase or (&or [t ge G`Base-1 : t in abcdef]) then
            // Assign the parameters to letters
            ijk := Reverse(IntegerToSequence(G`ijk, 2));
            while #ijk lt 3 do
                Insert(~ijk, 1, 0);
            end while;
            i, j, k := Explode(ijk);

            while #abcdef lt 6 do
                Insert(~abcdef, 1, 0);
            end while;
            a, b, c, d, e, f := Explode(abcdef);

            // Cook a curve
            if G`method eq 1 then
                if (i eq 0 and (d gt 0 or a gt 0)) or 
                    (j eq 0 and (e gt 0 or b gt 0)) or
                    (k eq 0 and (f gt 0 or c gt 0)) then
                    continue;
                end if;
                a2 := i*G`pi^d * G`u^a;
                a4 := j*G`pi^e * G`u^b;
                a6 := k*G`pi^f * G`u^c;
            else //method eq 2
                if (i eq 0 and (a gt 0 or b gt 0)) or 
                    (j eq 0 and (c gt 0 or d gt 0)) or
                    (k eq 0 and (e gt 0 or f gt 0)) then
                    continue;
                end if;
                a2 := i*G`pi^a * G`u^b;
                a4 := j*G`pi^c * G`u^d;
                a6 := k*G`pi^e * G`u^f;
            end if;
            found, E := IsEllipticCurve([G`F!0,a2,0,a4,a6]);
            if found and (Valuation(jInvariant(E)) lt 0) and (Valuation(Discriminant(E)) gt 0) then
                found := false;
            elif found then
                a,b,c,d,e,f,G`counter,G`Base;
                //i,j,k,a,b,c,d,e,f;
                G`curve := E;
            end if;
        else
            found := false;
        end if;
    until found;

    return E;
end intrinsic;

function mTorsionField(E1, m)
    //We Pick and Elliptic Curve and a WeierstrassModel y^2=f(x)
    F := BaseRing(E1);
    E := WeierstrassModel(E1);
    
    // Then we adjoint the roots of f(x) to Q9 to obtain a field L;
    f := HyperellipticPolynomials(E);

    g := DivisionPolynomial(E,m);
    L, roots := SplittingField(g);
    R<x> := PolynomialRing(L);
    // g2 := R!g;
    // roots := Roots(g2);

    if m eq 3 then
        r:=roots[1]; 
        z1 := Evaluate(R!f,r);
        L := SplittingField(R!(x^2-z1));
        R<x> := PolynomialRing(L);
    else
        for r in roots do
            z1 := Evaluate(R!f,r);
            L := SplittingField(R!(x^2-z1));
            R<x> := PolynomialRing(L);
        end for;
    end if;
    return L;
end function;

function E3TorsField(E1)
    return mTorsionField(E1, 3);
end function;

function FundamentalTwist(Twist)
    test:=[];
    FTwist:=[];
    F:=Parent(Twist[1]);
    R<x> := PolynomialRing(F);
    Sel,FtoSel := pSelmerGroup(2,F);
    SeltoF := Inverse(FtoSel);
    for t in Twist do
        if RamificationDegree(SplittingField(x^2-t),F) eq 1 then sun:=FtoSel(t); end if;
    end for;

    for t in Twist do
    s:=FtoSel(t);
    if (not s eq sun) and (not s in test) and (not s*sun in test) then test:=Append(test,s); FTwist:=Append(FTwist,t); end if;  
    end for;

    return FTwist;
end function;

intrinsic MatchType(E::EllCrv, CandidateTypes::SeqEnum[InType]) -> InType, RngIntElt
{Returns the inertial type of the elliptic curve E, if found in the provided sequence.
Second output returns the index of the type in the sequence, or 0 if not found.}
    L := E3TorsField(E);
    return FindInType(L, CandidateTypes);
end intrinsic;

function FindPS(F,PS,SCU,SCR,Ex8,Ex24,AllCurves,Twist,FTwist)
    FTwist := [1] cat FTwist;

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

    p, ram_deg, in_deg, pi, N := BaseValues(F);

    SCRc  := AssociativeArray();
    for i in [1..#Twist] do
        for tau in SCR do
            if not IsSquare(tau`Character`Field!Twist[i]) then
                continue;
            end if;

            if not (tau`CondExp in Keys(SCRc)) then
                SCRc[tau`CondExp]:= AssociativeArray();
            end if;

            if not i in Keys(SCRc[tau`CondExp]) then 
                SCRc[tau`CondExp,i]:=[tau]; 
                AllCurves["SCR",[i,tau`CondExp]]:=[* *]; 
            else
                Append(~SCRc[tau`CondExp,i], tau);
            end if;
        end for;
    end for;

    ECGenerator := EllipticCurveGenerator(F : InitialBase := 2, method := 2);
    while &or [#c gt 0 : c in PSc] do
        E := Next(ECGenerator);

        CondExp := Valuation(Conductor(E));

        L := E3TorsField(E);
        e := RamificationDegree(L,F);
        abelian := IsAbelian(L,F);

        if e lt 8 and abelian then//PS
            follow := false; i := 1;
            repeat 
                E1 := QuadraticTwist(E,FTwist[i]);
                CondExp1 := Valuation(Conductor(E1));
                i +:= 1;

                if not CondExp1 in Keys(PSc) or IsEmpty(PSc[CondExp1]) then continue; end if;

                L := i eq 1 select L else E3TorsField(E1);
                tau := FindInType(L, PSc[CondExp1]);
                    
                if IsNull(tau) then continue; end if;
                vprintf InTypes : "Found curve (PS) %o\n", E1;

                Exclude(~PSc[CondExp1], tau);
                Append(~AllCurves["PS",CondExp1],[*E1,tau*]);
                follow := true;
                tau;
                [#c: c in PSc];
            until not (follow and i le #FTwist);
        elif e lt 8 and not abelian then//SCU
            vprint InTypes : "SCU";
            i := 1;
            repeat 
                E1 := QuadraticTwist(E,FTwist[i]);
                CondExp1 := Valuation(Conductor(E1));
                i +:= 1;

                if not CondExp1 in Keys(SCUc) or IsEmpty(SCUc[CondExp1]) then continue; end if;

                EK1 := BaseChange(E1,SCUc[CondExp1][1]`Character`Field);
                L := E3TorsField(EK1);
                tau := FindInType(L, SCUc[CondExp1]);
                    
                if IsNull(tau) then continue; end if;
                vprintf InTypes : "Found curve (SCU) %o\n", EK1;

                Exclude(~SCUc[CondExp1], tau);
                Append(~AllCurves["SCU",CondExp1],[*EK1,tau*]);
                tau;
                [#c: c in SCUc];
            until i gt #FTwist;
        elif e eq 8 and ((in_deg mod 2 eq 1) or Degree(L,F) ge 24) then//SCR
            for i in Keys(SCRc[CondExp]) do
                if IsEmpty(SCRc[CondExp,i]) then continue; end if;
                time if not (IsSquare(L!Twist[i])) then continue; end if;
                time if not((Valuation(L!Discriminant(QuadraticTwist(E,Twist[i]))) mod 12 eq 0)) then continue;end if;
                time if not (Valuation(Conductor(BaseChange(QuadraticTwist(E,Twist[i]),L))) eq 0) then continue; end if;

                for t in FTwist do
                    E1 := QuadraticTwist(E,t);
                    CondExp1 := Valuation(Conductor(E1));
                    
                    if IsEmpty(SCRc[CondExp1,i]) then continue; end if;

                    EK1 := BaseChange(E1,SCRc[CondExp1,i,1]`Character`Field);
                    L := E3TorsField(EK1);
                    tau, pos := FindInType(L, SCRc[CondExp1,i]);

                    if IsNull(tau) then continue; end if;
                    vprintf InTypes : "Found curve (SCR) %o\n", EK1;

                    Remove(~SCRc[CondExp1,i],pos);
                    Append(~AllCurves["SCR",[i,CondExp1]],[*E1,tau*]);
                    tau;
                    [#c : c in SCRc[CondExp]];
                end for;
            end for;
        end if;
    end while;
    return AllCurves;
end function;

function FindSCU(F,SCU,AllCurves,FTwist)
    SCUc  := AssociativeArray();
    for tau in SCU do
        if not (tau`CondExp in Keys(SCUc)) then
            SCUc[tau`CondExp] := [tau];
            AllCurves["SCU",tau`CondExp] := [* *];
        else
            Append(~SCUc[tau`CondExp], tau);
        end if;
    end for;

    ECGenerator := EllipticCurveGenerator(F : InitialBase := 2, method := 2);
    i := 0;
    while &or [#c gt 0 : c in SCUc] do
        E := Next(ECGenerator);

        CondExp := Valuation(Conductor(E));
        if not CondExp in Keys(SCUc) or IsEmpty(SCUc[CondExp]) then continue; end if;

        L := E3TorsField(E);
        if (RamificationDegree(L,F) ge 8) then 
            continue; 
        elif IsAbelian(L,F) then 
            continue; 
        else
            EK := BaseChange(E,SCUc[CondExp][1]`Character`Field);
            L := E3TorsField(EK);
            tau := FindInType(L, SCUc[CondExp]);

            if IsNull(tau) then continue; end if;

            vprintf InTypes : "Found curve (SCU) %o\n", E;
            Exclude(~SCUc[CondExp], tau);
            Append(~AllCurves["SCU",CondExp], [*E,tau*]);
            tau;
            i+:=1;i;
            
            for t in FTwist do
                E1 := QuadraticTwist(E,t);
                CondExp1 := Valuation(Conductor(E1));

                if not CondExp1 in Keys(SCUc) or IsEmpty(SCUc[CondExp1]) then continue; end if;

                EK1 := BaseChange(E1,SCUc[CondExp1][1]`Character`Field);
                L := E3TorsField(EK1);
                tau := FindInType(L, SCUc[CondExp1]);

                if IsNull(tau) then continue; end if;
            
                vprintf InTypes : "Found curve (SCU) %o\n", E1;
                Exclude(~SCUc[CondExp1], tau);
                Append(~AllCurves["SCU", CondExp1], [*E1,tau*]);
                tau;
                i+:=1;i;
            end for;
        end if;
    end while;
    return AllCurves;
end function;

function FindSCR(F,SCR,AllCurves,Twist,FTwist)
    FTwist := [1] cat FTwist;
    p, ram_deg, in_deg, pi, N := BaseValues(F);

    SCRc  := AssociativeArray();
    for i in [1..#Twist] do
        for tau in SCR do
            if not IsSquare(tau`Character`Field!Twist[i]) then
                continue;
            end if;

            if not (tau`CondExp in Keys(SCRc)) then
                SCRc[tau`CondExp]:= AssociativeArray();
            end if;

            if not i in Keys(SCRc[tau`CondExp]) then 
                SCRc[tau`CondExp,i]:=[tau]; 
                AllCurves["SCR",[i,tau`CondExp]]:=[* *]; 
            else
                Append(~SCRc[tau`CondExp,i], tau);
            end if;
        end for;
    end for;

    ECGenerator := EllipticCurveGenerator(F : InitialBase := 2, method := 1);
    while &or [#c gt 0 : c in d, d in SCRc] do
        E := Next(ECGenerator);
        
        CondExp := Valuation(Conductor(E));
        if CondExp notin Keys(SCRc) then continue; end if;

        L := E3TorsField(E);
        d := Degree(L,F);

        if not (RamificationDegree(L,F) eq 8) then 
            continue; 
        elif (in_deg mod 2 eq 0) and Degree(L,F) ge 24 then 
            continue; 
        else
            for i in Keys(SCRc[CondExp]) do
                // if IsEmpty(SCRc[CondExp,i]) then continue; end if;
                // if not (IsSquare(L!Twist[i])) then continue; end if;
                // time if not((Valuation(L!Discriminant(QuadraticTwist(E,Twist[i]))) mod 12 eq 0)) then continue;end if;
                // time if not (Valuation(Conductor(BaseChange(QuadraticTwist(E,Twist[i]),L))) eq 0) then continue; end if;

                for t in FTwist do
                    E1 := QuadraticTwist(E,t);
                    CondExp1 := Valuation(Conductor(E1));
                    
                    if i notin Keys(SCRc) or IsEmpty(SCRc[CondExp1,i]) then continue; end if;

                    EK1 := BaseChange(E1,SCRc[CondExp1,i,1]`Character`Field);
                    L := E3TorsField(EK1);
                    tau, pos := FindInType(L, SCRc[CondExp1,i]);

                    if IsNull(tau) then continue; end if;
                    vprintf InTypes : "Found curve (SCR) %o\n", EK1;

                    Remove(~SCRc[CondExp1,i],pos);
                    Append(~AllCurves["SCR",[i,CondExp1]],[*E1,tau*]);
                    tau;
                    &+[#c : c in AllCurves["SCR"]];
                end for;
            end for;
        end if;
    end while;
end function;

intrinsic FindAllCurves(F::FldPad) -> .
{}
    time PS, SCU, SCR, Ex8, Ex24, Twist := InTypes(F : SkipExceptionals:=true);

    FTwist:=FundamentalTwist(Twist);
    AllCurves:=AssociativeArray();
    AllCurves["PS"] := AssociativeArray();
    AllCurves["SCU"] := AssociativeArray();
    AllCurves["SCR"] := AssociativeArray();
    AllCurves["Ex8"] := AssociativeArray();
    AllCurves["Ex24"] := AssociativeArray();

    // time AllCurves := FindPS(F,PS,SCU,SCR,Ex8,Ex24,AllCurves,Twist,FTwist);
    // time AllCurves := FindSCU(F,SCU,AllCurves,FTwist);
    time AllCurves := FindSCR(F,SCU,AllCurves,Twist,FTwist);

    return AllCurves;

end intrinsic;