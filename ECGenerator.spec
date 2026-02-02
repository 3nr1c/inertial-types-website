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
    OF:=Integers(F);
    for x1,x2 in [0..10] do
        z:=F![x1,x2];
        if IsUnit(OF!z) and not (z in BaseRing(F)) then z; ECG`u := z; break x1;  end if;
    end for;
    ECG`Base := InitialBase;
    ECG`InitialBase := ECG`Base;
    ECG`ijk := 1;
    ECG`counter := -1;
    ECG`method := method;
    return ECG;
end intrinsic;

// function NextMethod1(G)
// end function;

intrinsic Next(G::CrvEllGenerator) -> CrvEll
{Return a new elliptic curve according to the internal state of the generator}
    found := false;
    repeat
        G`counter +:= 1;
        if G`counter gt (G`Base^6 - 1) then
            G`ijk +:= 1;
            G`counter := 0;
            if G`ijk gt 7 then
                G`ijk := 1;
                G`Base +:= 1;
            end if;
        end if;

        abcdef := Reverse(IntegerToSequence(G`counter, G`Base));
        if G`Base eq G`InitialBase or (&or [t ge G`Base-1 : t in abcdef]) then
            // Assign the parameters to letters
            ijk := Reverse(IntegerToSequence(G`ijk, 2));
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
                if (i eq 0 and (d gt 0 or a gt 0)) or 
                    (j eq 0 and (e gt 0 or b gt 0)) or
                    (k eq 0 and (f gt 0 or c gt 0)) then
                    continue;
                end if;
                a2 := i*G`pi^d * G`u^a;
                a4 := j*G`pi^e * G`u^b;
                a6 := k*G`pi^f * G`u^c;
            else //method eq 2
                if (i eq 0 and (a gt 0 or b gt 0)) or 
                    (j eq 0 and (c gt 0 or d gt 0)) or
                    (k eq 0 and (e gt 0 or f gt 0)) then
                    continue;
                end if;
                a2 := i*G`pi^a * G`u^b;
                a4 := j*G`pi^c * G`u^d;
                a6 := k*G`pi^e * G`u^f;
            end if;
            found, E := IsEllipticCurve([G`F!0,a2,0,a4,a6]);
            if found and (Valuation(jInvariant(E)) lt 0) then
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