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

function InertialType(E);
    F := BaseRing(E);
    p := Prime(F);
    if p eq 2 then m := 3; else m := 5; end if;
    L := mTorsionField(E,m);
    d := Degree(L,F);
    e := RamificationDegree(L,F);
    if p eq 2 then
        if d eq 24 then
            if e eq 8 then print("Exceptional Q8");
            else print("Exceptional SL2F3"); end if;
        elif IsAbelian(L,F) then 
            print("PrincipalSeries");

            r := 10;
            

        elif RamificationDegree(L,F) lt 8 then print("SCU");
        else print("SCR");
        end if;
    elif p eq 3 then
        if IsAbelian(L,F) then print("PrincipalSeries");
        elif RamificationDegree(L,F) lt 8 then print("SCU");
        else print("SCR");
        end if;
    end if;
return 0;
end function;