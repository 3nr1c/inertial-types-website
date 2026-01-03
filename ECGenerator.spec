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
    ECG`u := 1 + ECG`pi;
    ECG`Base := InitialBase;
    ECG`InitialBase := ECG`Base;
    ECG`ijk := 1;
    ECG`counter := -1;
    ECG`curve := EllipticCurveWithjInvariant(1/pi);
    ECG`method := method;
    return ECG;
end intrinsic;

intrinsic Next(G::CrvEllGenerator) -> CrvEll
{Return a new elliptic curve according to the internal state of the generator}
    found := false;
    repeat
        // The following prevents stalling if either of i,j,k is zero
        // Change always accordingly with the formulas for a2, a4, a6 below
        if G`method eq 1 then
            if G`ijk mod 2 eq 1 then // k eq 1
                G`counter +:= 1;
            elif G`ijk mod 4 eq 2 then // j eq 1
                G`counter +:= G`Base;
            else // i eq 1
                G`counter +:= (G`Base)^2;
            end if;
        else //method eq 2
            if G`ijk mod 2 eq 1 then // k eq 1
                G`counter +:= 1;
            elif G`ijk mod 4 eq 2 then // j eq 1
                G`counter +:= (G`Base)^2;
            else // i eq 1
                G`counter +:= (G`Base)^4;
            end if;
        end if;

        if G`counter gt (G`Base^6 - 1) then
            G`ijk +:= 1;
            G`counter := 0;
            if G`ijk gt 7 then
                G`ijk := 1;
                G`Base +:= 1;
            end if;
        end if;

        abcdef := IntegerToSequence(G`counter, G`Base);
        if G`Base eq G`InitialBase or (&or [t ge G`Base-1 : t in abcdef]) then
            // Assign the parameters to letters
            ijk := IntegerToSequence(G`ijk, 2);
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
                a2 := i*G`pi^d * G`u^a;
                a4 := j*G`pi^e * G`u^b;
                a6 := k*G`pi^f * G`u^c;
            else //method eq 2
                a2 := i*G`pi^a * G`u^b;
                a4 := j*G`pi^c * G`u^d;
                a6 := k*G`pi^e * G`u^f;
            end if;
            found, E := IsEllipticCurve([G`F!0,a2,0,a4,a6]);
            if found and (Valuation(jInvariant(E)) lt 0 or IsIsomorphic(E, G`curve)) then
                found := false;
            elif found then
                // i,j,k,a,b,c,d,e,f;
                G`curve := E;
            end if;
        else
            found := false;
        end if;
    until found;

    return E;
end intrinsic;