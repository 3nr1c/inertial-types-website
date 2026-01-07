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

function OptimalNorms(L,F,f)

r:=RamificationDegree(L,F);
c:=Max(r*(f-1)+1,AbsoluteRamificationDegree(L)+1);
assert Ceiling(c/r) ge f;
LowPrecL:=ChangePrecision(L,c);
OL:=Integers(LowPrecL);
UL,ULtoOL:=UnitGroup(OL);
GenUL:=SetToSequence(Generators(UL));

return [ChangePrecision(Norm(ChangePrecision(L!LowPrecL!ULtoOL(g),Precision(L)),F),Precision(F)) :g in GenUL],[ChangePrecision(L!LowPrecL!ULtoOL(g),Precision(L)) :g in GenUL];

end function;
