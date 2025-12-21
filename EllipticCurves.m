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

    for r in roots do
        z1 := Evaluate(R!f,r[1]);
        L := SplittingField(R!(x^2-z1));
        R<x> := PolynomialRing(L);
    end for;

    return L;
end function;


function FindChar(L,chars,group,lift,d)
    K:=Codomain(lift);
    exp:=Max(d,AbsoluteRamificationDegree(L)+1);
    L1:=ChangePrecision(L,exp);
    OL:=Integers(L1);
    UL,ULtoOL:=UnitGroup(OL);
    Gen:=[g : g in Generators(UL)];
    Norms:=[Inverse(lift)(Norm(ChangePrecision(L!L1!ULtoOL(g),Precision(L)),K)): g in Gen];
    for g in Norms do   
        chars:=[c : c in chars | IsIdentity(c`Map(g))];
    end for;
    if IsEmpty(chars) then return 0; else return chars[1]; end if;
end function;

function FindSCRChar(E,L,Twist,SCRChars,SCRGroups,SCRLifts,SCRexp)
    F:=BaseRing(E);
    p, ram_deg, in_deg, pi, N := BaseValues(F);
    if p eq 2 then m := 3; else m := 5; end if;
    Lx<x>:=PolynomialRing(L);
    Inductions:=[];
    for j in [1..#Twist] do
        if not IsEmpty(Roots(x^2-Twist[j])) then
            Inductions:=Append(Inductions,j);
            Inductions;  
        end if;          
    end for;

    if (in_deg mod 2 eq 0) then
        Chars:=[* *];
        for j in Inductions do
            E1:=BaseChange(E,Codomain(SCRLifts[j]));
            L:= mTorsionField(E1,m);
            chi:=FindChar(L,SCRChars[j],SCRGroups[j],SCRLifts[j],SCRexp[j]);
            Chars:=Append(Chars,chi);
        end for;
        return Chars;
    else
        for j in Inductions do
            if Valuation(Conductor(BaseChange(QuadraticTwist(E,Twist[j]),L))) eq 0 then
                E1:=BaseChange(E,Codomain(SCRLifts[j]));
                L:= mTorsionField(E1,m);
                chi:=FindChar(L,SCRChars[j],SCRGroups[j],SCRLifts[j],SCRexp[j]);
                return chi;
            end if;
        end for;
    end if;
end function;


function InTypeOf(E,Twist,PSChar,PSGroup,PSLift,PSExp,SCUChars,SCUGroup,SCULift,SCUexp,SCRChars,SCRGroups,SCRLifts,SCRexp,Ex8Chars,Ex8Group,Ex8Lift,Ex8exp,Ex24Chars,Ex24Groups,Ex24Lifts,Ex24exp);
    F := BaseRing(E);
    p, ram_deg, in_deg, pi, N := BaseValues(F);
    if p eq 2 then m := 3; else m := 5; end if;
    L := mTorsionField(E,m);
    d := Degree(L,F);
    e := RamificationDegree(L,F);
    if p eq 2 then
        if d eq 24 then
            if e eq 8 then 
                print("Exceptional Q8");
                E1:=BaseChange(E,Codomain(Ex8Lift));
                L:=mTorsionField(E1,m);
                chi:= FindChar(L,Ex8Chars,Ex8Group,Ex8Lift,Ex8exp);
            else 
                print("Exceptional SL2F3");
                Lx<x>:=PolynomialRing(L);
                chi:=[* *];
                for i in [1..#Ex24Groups] do
                    K:=BaseRing(Codomain(Ex24Lifts[i,1]));
                    
                    if not IsEmpty(Roots(Lx!DefiningPolynomial(K,Q4))) then 
                        for k in [1..#Ex24Chars[i]] do
                            i,k;
                            E1:=BaseChange(E,Codomain(Ex24Lifts[i,k]));
                            time L:= mTorsionField(E1,m);
                            time char:=FindChar(L,Ex24Chars[i,k],Ex24Groups[i,k],Ex24Lifts[i,k],Ex24exp[i,k]);
                            print("------------------------");
                            if not Type(char) eq HomGrp then continue; end if;
                            chi:=Append(chi,char);
                        end for;   
                    end if;     
                end for;
            end if;
        elif IsAbelian(L,F) then 
            print("PrincipalSeries");
            chi:=FindChar(L,PSChar,PSGroup,PSLift,PSExp);
        elif RamificationDegree(L,F) lt 8 then
            print("SCU");
            E1:=BaseChange(E,Codomain(SCULift));
            L:= mTorsionField(E1,m);
            chi:=FindChar(L,SCUChars,SCUGroup,SCULift,SCUexp);
        else 
            print("SCR");
            chi:=FindSCRChar(E,L,Twist,SCRChars,SCRGroups,SCRLifts,SCRexp);



        end if;
    elif p eq 3 then
        if IsAbelian(L,F) then
            print("PrincipalSeries");
            chi:=FindChar(L,PSChar,PSGroup,PSLift,PSExp);
        elif RamificationDegree(L,F) lt 8 then 
            print("SCU");
            chi:=FindChar(L,SCUChars,SCUGroup,SCULift,SCUexp);
        else print("SCR");
        end if;
    end if;
return chi;
end function;