function mTorsionField(E1, m)
    //We Pick and Elliptic Curve and a WeierstrassModel y^2=f(x)
    F := BaseRing(E1);
    P<x> := PolynomialRing(F);
    E := WeierstrassModel(E1);
    
    // Then we adjoint the roots of f(x) to Q9 to obtain a field L;
    v2 := aInvariants(E);
    f := x^3+v2[2]*x^2+v2[4]*x+v2[5]*1;

    g := DivisionPolynomial(E,m);
    L := SplittingField(g);
    R<x> := PolynomialRing(L);
    g2 := R!g;
    roots := Roots(g2);

    if m eq 3 then
        r:=roots[1]; 
        z1 := Evaluate(R!f,r[1]);
        L := SplittingField(R!(x^2-z1));
        R<x> := PolynomialRing(L);
    else
        for r in roots do
            z1 := Evaluate(R!f,r[1]);
            L := SplittingField(R!(x^2-z1));
            R<x> := PolynomialRing(L);
        end for;
    end if;
    return L;
end function;

function FindInertiaType(L, CandidateTypes)
    // Warning: this function will only work if all the candidate types
    // have a character with same Field, GrpExp and Lift
    chi := CandidateTypes[1]`Character;
    K := chi`Field;
    exp := Max(chi`GrpExp, AbsoluteRamificationDegree(L) + 1);
    lift := chi`Lift;

    L1 := ChangePrecision(L, exp);
    OL := Integers(L1);
    UL, ULtoOL := UnitGroup(OL);
    Gen := [g : g in Generators(UL)];
    Norms:=[Inverse(lift)(Norm(ChangePrecision(L!L1!ULtoOL(g),Precision(L)),K)): g in Gen];
    for tau in CandidateTypes do
        found := true;
        for g in Norms do
            if not IsIdentity(tau`Character(g)) then
                found := false;
                break;
            end if;
        end for;
        if found then return tau; end if;
    end for;
    return 0;
end function;

function FindSCRType(E,L,Twist,SCR)
    F:=BaseRing(E);
    p, ram_deg, in_deg, pi, N := BaseValues(F);
    if p eq 2 then m := 3; else m := 5; end if;
    Lx<x>:=PolynomialRing(L);
    Inductions:=[];
    for j in [1..#Twist] do
        if IsEmpty(SCR[j]) then continue; end if;
        if not IsEmpty(Roots(x^2-Lx!Twist[j])) then    
            Inductions:=Append(Inductions,j);
            Inductions;  
        end if;          
    end for;

    if (in_deg mod 2 eq 0) then
        Chars:=[* *];
        for j in Inductions do
            E1:=BaseChange(E,SCR[j][1]`Character`Field);
            L:= mTorsionField(E1,m);
            E1;
            chi:=FindInertiaType(L,SCR[j]);
            Chars:=Append(Chars,chi);
        end for;
        return Chars;
    else
        for j in Inductions do
            if Valuation(Conductor(BaseChange(QuadraticTwist(E,Twist[j]),L))) eq 0 then
                E1:=BaseChange(E,SCR[j][1]`Character`Field);
                L:= mTorsionField(E1,m);
                chi:=FindInertiaType(L,SCR[j]);
                if Type(chi) eq RngIntElt then continue;
                else return chi; end if;
            end if;
        end for;
    end if;
    return 0;
end function;


function InTypeOf(E,Twist, PS, SCU, SCR, Ex8, Ex24);
    F := BaseRing(E);
    p, ram_deg, in_deg, pi, N := BaseValues(F);
    if p eq 2 then m := 3; else m := 5; end if;
    CondExp:=Valuation(Conductor(E));
    L := mTorsionField(E,m);
    d := Degree(L,F);
    e := RamificationDegree(L,F);
    chi:=0;
    if p eq 2 then
        if d ge 24 then
            if e eq 8 then
                if #Ex8 gt 0 then 
                    print("Exceptional Q8");
                    E1:=BaseChange(E,Ex8[1]`Character`Field);
                    L:=mTorsionField(E1,m);
                    chi:= FindInertiaType(L,Ex8);
                end if;
            else 
                if not [#Ex24[i] : i in [1..#Ex24]] eq [0 : j in [1..#Ex24]] then
                    print("Exceptional SL2F3");
                    Lx<x>:=PolynomialRing(L);
                    chi:=[* *];
                    for i in [1..#Ex24] do
                        if #Ex24[i] gt 0 then
                            K := Ex24[i][1]`Character`Field;

                            if not IsEmpty(Roots(Lx!DefiningPolynomial(K,F))) then 
                                E1:=BaseChange(E,Ex24[i][1]`Character`Field);
                                time L := mTorsionField(E1, m);
                                time char := FindInertiaType(L, Ex24[i]);
                                print("------------------------");
                                return char;
                                if Type(char) eq RngIntElt then continue; end if;
                                chi:=char;
                            end if;
                        end if;
                    end for;
                end if;
            end if;
        elif IsAbelian(L,F) then
            if #PS gt 0 then  
                print("PrincipalSeries");
                chi:=FindInertiaType(L,PS);
            end if;
        elif RamificationDegree(L,F) lt 8 then
            if #SCU gt 0 then
                print("SCU");
                E1:=BaseChange(E,SCU[1]`Character`Field);
                L:= mTorsionField(E1,m);
                chi:=FindInertiaType(L,SCU);
            end if;
        else 
            if not [#SCR[i] : i in [1..#SCR]] eq [0 : j in [1..#SCR]] then
                print("SCR");
                chi:=FindSCRType(E,L,Twist,SCR);//Chars,SCRGroups,SCRLifts,SCRexp);
            end if;    
        end if;

    elif p eq 3 then
        if IsAbelian(L,F) then
            print("PrincipalSeries");
            chi:=FindInertiaType(L,PS);
        elif RamificationDegree(L,F) lt 8 then 
            print("SCU");
            chi:=FindInertiaType(L,SCU);
        else print("SCR");
            chi:=FindSCRType(E,L,Twist,SCR);//Chars,SCRGroups,SCRLifts,SCRexp);
        end if;
    end if;
return chi;
end function;