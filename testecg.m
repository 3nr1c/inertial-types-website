Attach("ECGenerator.spec");

function Generate1000Curves()
    Q2 := pAdicField(2,100);
    F := FieldOfFractions(AllExtensions(Q2,2)[1]);

    ECG := EllipticCurveGenerator(F);
    curves := [];
    i := 0;
    while #curves lt 1000 do
        E := Next(ECG);
        found := false;
        for E1 in curves do
            found := found or IsIsomorphic(E,E1);
            if found then break; end if;
        end for;
        if not found then 
            Append(~curves, E);
            ECG`ijk,ECG`counter,i,#curves;
        end if;
        i+:=1;
    end while;
    return 0;
end function;

function Generate1000jInvariants()
    Q2 := pAdicField(2,100);
    F := FieldOfFractions(AllExtensions(Q2,2)[1]);

    ECG := EllipticCurveGenerator(F);
    js := [];
    i := 0;
    while #js lt 1000 do
        E := Next(ECG);
        found := jInvariant(E) in js;
        if not found then 
            Append(~js, jInvariant(E));
            ECG`ijk,ECG`counter,i,#js;
        end if;
        i+:=1;
    end while;
    return 0;
end function;