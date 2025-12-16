function AllQuadraticExtensions(F)
    R<x> := PolynomialRing(F);
    Sel,FtoSel := pSelmerGroup(2,F);
    SeltoF := Inverse(FtoSel);

    Extensions := [];
    Twist:=[];
    for s in Sel do
        if IsIdentity(s) then continue; end if;
        z:=ChangePrecision(SeltoF(s), Precision(F));
        Append(~Twist,z);
        Append(~Extensions, SplittingField(x^2 - z));
    end for;

    return Extensions, Twist;
end function;