load "Main.m";
load "EllipticCurves.m";

//Extensions, Twists := AllQuadraticExtensions(Q2);
K := Q2;//Extensions[1];

Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(K);
p, ram_deg, in_deg, pi, N := BaseValues(K);
// Fp, proj := ResidueClassField(Integers(K));
u := 1 + pi;

VisitedCurves := [];

for a, b, c, d, e, f in [0..5] do
    a,b,c,d,e,f;
    a2 := pi^a * u^b;
    a4 := pi^c * u^d;
    a6 := pi^e * u^f;

    isEC, E := IsEllipticCurve([0,a2,0,a4,a6]);
    visited := false;
    for E1 in VisitedCurves do
        if IsIsomorphic(E, E1) then 
            visited := true;
            break;
        end if;
    end for;
    if visited then continue; 
    else Append(~VisitedCurves, E); end if;

    if not isEC then continue; end if;
    E;
    tau := InTypeOf(E, Twist, PS, SCU, SCR, Ex8, Ex24);
    tau;
end for;