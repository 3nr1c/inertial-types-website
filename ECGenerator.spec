declare type CrvEllGenerator;
declare attributes CrvEllGenerator:
    F,
    pi,
    u,
    InitialBase,
    Base,
    counter,
    ijk,
    curve
;

intrinsic EllipticCurveGenerator(F::FldPad : InitialBase := 2) -> CrvEllGenerator 
{Create an object that yields elliptic curves over F with potentially good reduction}
    ECG := New(CrvEllGenerator);
    ECG`F := F;
    pi := UniformizingElement(F);
    ECG`pi := pi;
    ECG`u := 1 + ECG`pi;
    ECG`Base := InitialBase;
    ECG`InitialBase := ECG`Base;
    ECG`ijk := -1;
    ECG`counter := -1;
    ECG`curve := EllipticCurveWithjInvariant(1/pi);
    return ECG;
end intrinsic;

intrinsic Next(G::CrvEllGenerator) -> CrvEll
{Return a new elliptic curve according to the internal state of the generator}
    found := false;

    repeat
        // If we have exhausted the bound, increase it and run the function again
        if G`ijk eq 7 then 
            if G`counter ge (G`Base^6 - 1) then
                G`ijk := 0;
                G`Base +:= 1;
                // print("---------------------");print(G`Base);print("---------------------");
                return Next(G);
            else
                G`ijk := -1;
            end if;
        end if;

        // Advance the parameters i, j, k
        G`ijk +:= 1;
        // Assign the parameters to letters
        ijk := IntegerToSequence(G`ijk, 2);
        while #ijk lt 3 do
            Insert(~ijk, 1, 0);
        end while;
        i, j, k := Explode(ijk);

        if k eq 1 then
            G`counter +:= 1;
        elif j eq 1 then
            G`counter +:= (G`Base^2);
        else 
            G`counter +:= (G`Base^4);
        end if;


        abcdef := IntegerToSequence(G`counter, G`Base);
        if G`Base eq G`InitialBase or (&or [t ge G`Base-1 : t in abcdef]) then
            while #abcdef lt 6 do
                Insert(~abcdef, 1, 0);
            end while;
            a, b, c, d, e, f := Explode(abcdef);

            // Cook a curve
            a2 := i*G`pi^a * G`u^b;
            a4 := j*G`pi^c * G`u^d;
            a6 := k*G`pi^e * G`u^f;
            found, E := IsEllipticCurve([G`F!0,a2,0,a4,a6]);
            if found and (Valuation(jInvariant(E)) lt 0 or IsIsomorphic(E, G`curve)) then
                found := false;
            elif found then
                G`curve := E;
            end if;
        else
            found := false;
        end if;
    until found;

    return E;
end intrinsic;