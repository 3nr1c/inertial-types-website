intrinsic BetterPoly(L::FldPad, K::FldPad : minprec := 1)
    p := DefiningPolynomial(L, K);
    for prec in [minprec..Precision(K)] do
        Ksm := ChangePrecision(K, prec);
        p1 := ChangeRing(p, Ksm);
        betterp := ChangeRing(p1, K);

        if IsIrreducible(betterp) and HasRoot(betterp, L) then 
            break;
        end if;
    end for;
    return betterp;
end intrinsic;