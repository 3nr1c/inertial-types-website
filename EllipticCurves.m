function MySquarefreePart(f)

  // Easy cases: degree 1, not padics, p-adic of precision 0 (yuck)

  if Degree(f) le 1 then return f; end if;
  F:=BaseRing(f);
  if Type(F) eq RngPad then
    F:=FieldOfFractions(F);
    f:=PolynomialRing(F)!f;
  end if;
  if Type(F) ne FldPad then
    return SquarefreePart(f);
  end if;

  prec:=Precision(F);
  error if prec eq 0, "Cannot do much with p-adic of precision 0";

  R:=PolynomialRing(F);
  x := R.1;
  O:=Integers(F);
  k,m:=ResidueClassField(O);
  p:=Characteristic(k);

  // Cheap trick to make Derivative monic (for monic f) when p|degree

  fd:=f;
  if Degree(f) mod p eq 0 then
    v:=[Valuation(Evaluate(f,n)): n in [1..2*Degree(f)]];
    m,i:=Min(v);
    fd:=f*(x-i);
  end if;

  g:=GCD(f,Derivative(fd));

  plc:=Precision(LeadingCoefficient(g));
  d:=Degree(g);
  ok:=(d eq 0) and (plc gt prec/4) or (d gt 0) and (plc gt prec/2);
  error if not ok,
    "Not enough precision to determine whether the polynomial is square-free for\n";
    //"f="*DelSpaces(f)*" d="*DelSpaces(d)*" prec="*DelSpaces(prec)*" plc="*DelSpaces(plc);
  return (d eq 0) select f else (f div g);
end function;

function E3TorsField(E1)
    F:=BaseRing(E1);
    E := WeierstrassModel(E1);
    R<x>:=PolynomialRing(F);
    c4,c6:=Explode(cInvariants(E));
    L:=SplittingField(x^8-6*c4*x^4-8*c6*x^2-3*c4^2);
    return L;
end function;

function mTorsionField(E1, m)
    //We Pick and Elliptic Curve and a WeierstrassModel y^2=f(x)
    F := BaseRing(E1);
    E := WeierstrassModel(E1);
    
    // Then we adjoint the roots of f(x) to Q9 to obtain a field L;
    v2 := aInvariants(E);
    g := MySquarefreePart(DivisionPolynomial(E,m));
    L, roots := SplittingField(g);
    R<x> := PolynomialRing(L);
    // g2 := R!g;
    // roots := Roots(g2);

    if m eq 3 then
        r:=roots[1];
        z1:=(r^3+L!v2[2]*r^2+L!v2[4]*r+L!v2[5]); 
        if not z1 in L then print("NO ROOTS USING E3TORS"); Parent(z1); z1; [x in L : x in roots]; R; L; return E3TorsField(E); end if;
        L := SplittingField(R!(R!x^2-R!z1));
        R<x> := PolynomialRing(L);
    else
        for r in roots do
            z1:=L!(r^3+L!v2[2]*r^2+L!v2[4]*r+L!v2[5]);
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
    return New(NullIT);
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
                if IsNull(chi) then continue;
                else return chi; end if;
            end if;
        end for;
    end if;
    return New(NullIT);
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