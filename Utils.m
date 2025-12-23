function AllQuadraticExtensions(F : Selmer:=true)
    Extensions := [];
    Twist:=[];
    if Selmer then
        R<x> := PolynomialRing(F);
        Sel,FtoSel := pSelmerGroup(2,F);
        SeltoF := Inverse(FtoSel);

        for s in Sel do
            if IsIdentity(s) then continue; end if;
            z:=ChangePrecision(SeltoF(s), Precision(F));
            Append(~Extensions, SplittingField(x^2 - z));
            Append(~Twist, z);
        end for;
    else
        for Z in AllExtensions(F, 2) do
            Append(~Extensions, FieldOfFractions(Z));
            Append(~Twist, Discriminant(FieldOfFractions(Z), F));
        end for;
    end if;

    return Extensions, Twist;
end function;

function FastMap(m)
// Given two groups A,B and a map m define as a composite
// of different maps it returns the map that goes directly from A to B without 
// passing thorough all the composites.
    A:=Domain(m);
    B:=Codomain(m);
    Gens := [g : g in Generators(A)];
    Fmap:= Homomorphism(A, B, Gens, [m(g) : g in Gens]);
    return Fmap;
end function;