function AllQuadraticExtensions(F)
    R<x> := PolynomialRing(F);
    Sel,FtoSel := pSelmerGroup(2,F);
    SeltoF := Inverse(FtoSel);

    Extensions := [];
    for s in Sel do
        if IsIdentity(s) then continue; end if;
        Append(~Extensions, SplittingField(x^2 - ChangePrecision(SeltoF(s), Precision(F))));
    end for;

    return Extensions;
end function;