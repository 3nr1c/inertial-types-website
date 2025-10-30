load "inertial-types3.m";

F := UnramifiedExtension(Q2,14);
// K := FieldOfFractions(AllExtensions(F,2)[3]);
R<x> := PolynomialRing(F);
K := ext<F|x^2-UniformizingElement(F)>;

K;

p, ram_deg, in_deg, pi, N := BaseValues(F);
Cond, pi, Gal, y := ExtValues(F,K);
f := Max(N-Cond, 2*Cond);
c := Cond;

UGroups, UMaps, ULift := UComplex(F, f);
G := UGroups[f - c + 1];
if f - c + 1 eq 1 then
    llift := ULift;
else
    llift := Inverse(UMaps[f - c]) * ULift;
end if;
VarepsGenerators := {K!llift(g) : g in Generators(G)};

CGroups, CMaps, CLift := ConComplex(F, K, f);

proj := Inverse(CLift);
VarepsGenerators := {proj(g) : g in VarepsGenerators | not IsIdentity(proj(g))};

G := CGroups[1];
G;
Q, GtoQ := quo<G | n*G>;
Q;
n := 4;

Gen:=[Q.i : i in [1..#Generators(Q)]];
OrderNSeq := [i : i in [1..#Gen] | Order(Gen[i]) eq n];

function Filtration (Q,GtoQ,Groups,Maps,Lift,n)
    Gen:=[Q.i : i in [1..#Generators(Q)]];
    R:=Integers(n);
    Zn:=RSpace(R,1);
    Rf:=RSpace(R,#Gen);
    ExpSpace:=Rf;
    H:=Hom(Rf,Zn);

    for g in Gen do
        if not (Order(g) mod n eq 0) then
            OrdFil:=Order(g)*(H!ElementToSequence(g));
            ExpSpace:=ExpSpace meet Kernel(OrdFil);
        end if;
    end for;

    Fil:=[ExpSpace];
    for i in [1..(#Groups-1)] do
        Ker:=[Q!GtoQ(g) : g in Generators(Kernel(Maps[i]))];
        V:=Fil[i];
        for g in Ker do
            phi:=H!ElementToSequence(g);
            V:=V meet Kernel(phi); 
        end for;
        Fil:=Append(Fil,V);
    end for;
    return Fil,H,ExpSpace;
end function;

R:=Integers(n);
Zn:=RSpace(R,1);
Rf:=RSpace(R,#Gen + 1);
ExpSpace:=Rf;
H:=Hom(Rf,Zn);

for g in Gen do
    if not (Order(g) mod n eq 0) then
        OrdFil:=Order(g)*(H!(ElementToSequence(g) cat [0]));
        ExpSpace:=ExpSpace meet Kernel(OrdFil);
    end if;
end for;

// Varepsilon conditions
for g in VarepsGenerators do
    // ExpSpace := ExpSpace meet Kernel(H!(ElementToSequence(g) cat [2]));
    // Kernel(H!(ElementToSequence(g) cat [2]));
    ExpSpace := ExpSpace meet Kernel(H!(ElementToSequence(GtoQ(g)) cat [2]));
end for;

// y condition
// bar_y := proj(y);//
bar_y2 := GtoQ(proj(y^2));
if (in_deg mod 2) eq 0 then
    // (in_deg mod 2) eq 0 checks if x^2+x+1 splits in F
    // Triply imprimitive with n = 4, characters must be quadratic on y
    ExpSpace := ExpSpace meet Kernel(H!(ElementToSequence(bar_y2) cat [0]));
    // Kernel(2*H!(ElementToSequence(bar_y) cat [0]));
    // quadratic_filter := func< chi, lift | IsIdentity(chi(bar_y))>;
else
    // Simply imprimitive with n = 4, characters must *not* be quadratic on y
    ExpSpace := ExpSpace meet Kernel(H!(ElementToSequence(bar_y2) cat [2]));

    // quadratic_filter := func< chi, lift | not IsIdentity(chi(bar_y))>;
end if;

ZeroRow := [0 : _ in [1 .. #Gen]];
F := [Rf];

for k in [2..#OrderNSeq] do
    Condition := Kernel(H!(Insert(ZeroRow, OrderNSeq[k-1], 2)));
    Append(~F, F[k-1] meet Condition);
end for;

One := [];

for k in [1..#OrderNSeq] do
    OneRow := ZeroRow cat [0];
    OneRow[OrderNSeq[k]] := 1;
    OneRow[#Gen+1] := -1;
    // OneRow;
    F[k] := F[k] meet Kernel(H!OneRow);
    // F[k];
end for;

T := Time();
Exps := {v : v in F[k] meet ExpSpace, k in [1..#OrderNSeq] | v[OrderNSeq[k]] eq 1};
// Count := 0;
// for k in [1 .. #OrderNSeq] do  
//     // Exps := Exps join {v : v in F[k] meet ExpSpace | v[OrderNSeq[k]] eq 1};
// end for;
#Exps;
Time(T);

T2 := Time();
Fil,H,ExpSpace := Filtration(Q,GtoQ,CGroups, CMaps, CLift, n);
for v in Exps do
    vprime := Remove(ElementToSequence(v), #Gen+1);
    conductor := #Fil;
    while conductor gt 1 and
        (#Fil[#Fil - conductor + 1] eq #Fil[#Fil - conductor + 2]
        or ExpSpace!vprime in Fil[#Fil - conductor + 2]) do
        conductor -:= 1;
    end while;
    // conductor;
    // conductor := #Fil + 1 - Max({i : i in [1..#Fil] | ExpSpace!vprime in Fil[i]});
    // vprime;conductor;
end for;
Time(T2);