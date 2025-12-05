function TupleToSeq(t)
    return [x : x in t];
end function;

function CharactersOfOrder(G, n)
    Zn := AdditiveGroup(Integers(n));

    Q, GtoQ := quo<G | [n * g : g in Generators(G)]>;

    QZn, t := Hom(Q, Zn);
    QChars := {};
    for f in QZn do
        if not (-f in QChars) and Order(f) eq n then
            Include(~QChars, f);
        end if;
    end for;

    // Debugging code
    // [* [[*Order(chi),t(chi)(g),Order(g)*] : g in Generators(Q)] : chi in QChars *];

    return [*FastMap(GtoQ*(t(f))) : f in QChars*];
end function;

function CharacterExponents(Zn, r)
// This function returns the tuples (x1,...,xr)
// necessary to obtain all characters of exact order n,
// modulo Aut(Z/n)
    n := #Zn;
    ZeroDivisors := {Zn!i : i in [2 .. n] | Gcd(n,i) gt 1};

    exponents := {};
    for k in [1 .. r] do
        for e in CartesianProduct(
            <CartesianPower(ZeroDivisors, k-1), CartesianPower(Zn, r - k)>
        ) do
            Include(~exponents, TupleToSeq(e[1]) cat [Zn!1] cat TupleToSeq(e[2]));
        end for;
    end for;
    return exponents;
end function;

function OldFastCharactersOfPrimePowerOrder(G, n)
    ZZ := Integers();
    Zn := AdditiveGroup(Integers(n));
    Q, GtoQ := quo<G | [n * g : g in Generators(G)]>;
    Gens := Generators(Q);
    GensOfOrder_n := [g : g in Gens | Order(g) eq n];
    GensOfLowerOrder := [g : g in Gens | Order(g) lt n];
    // Build Gens again so it keeps consecutive ordering
    Gens := GensOfOrder_n cat GensOfLowerOrder;

    QChars := [* *];
    if #GensOfOrder_n eq 0 then return QChars; end if;

    CharExponents := CharacterExponents(Zn, #GensOfOrder_n);
    if #GensOfLowerOrder gt 0 then
        LowerOrderExponents := {
            e : e in CartesianProduct(
                < {Zn!t : t in [0 .. n by ZZ!(n/Order(g))]} : g in GensOfLowerOrder >
            )
        };
        CharExponents := {
            e[1] cat TupleToSeq(e[2]) : e in CartesianProduct(
                CharExponents, LowerOrderExponents
            )
        };
    end if;
    for e in CharExponents do
        Append(~QChars, Homomorphism(Q, Zn, Gens, e));
    end for;

    // Debugging code
    // [* [chi(g) : g in Gens] : chi in QChars *];

    return [*FastMap(GtoQ*f) : f in QChars*];
end function;

function FastMapSum(f, g) 
    A:=Domain(f);
    B:=Codomain(f);
    Gens := [x : x in Generators(A)];
    Fmap:= Homomorphism(A, B, Gens, [f(x) + g(x) : x in Gens]);
    return Fmap;
end function;

function FastCharactersOfPrimePowerOrder(G, Maps, l, b: Elements:=[], Values:=[])
    assert #Elements eq #Values;
    n := l^b;
    Q, GtoQ := quo<G | n*G>;

    Gen:=[Q.i : i in [1..#Generators(Q)]];
    OrderNSeq := [i : i in [1..#Gen] | Order(Gen[i]) eq n];
    R:=Integers(n);
    Rf:=RSpace(R,#Gen + 1);
    ExpSpace:=Rf;
    H:=Hom(Rf,RSpace(R,1));

    // Equations to match the order of generating elements
    for g in Gen do
        if not (Order(g) mod n eq 0) then
            OrdFil:=Order(g)*(H!(ElementToSequence(g) cat [0]));
            ExpSpace:=ExpSpace meet Kernel(OrdFil);
        end if;
    end for;

    // We add the external conditions
    for i in [1 .. #Elements] do
        ExpSpace := ExpSpace meet 
            Kernel(H!(ElementToSequence(GtoQ(Elements[i])) cat [Values[i]]));    
    end for;

    ZeroRow := [0 : _ in [1 .. #Gen]];
    Fks := [Rf];


    for k in [2..#OrderNSeq] do
        Condition := Kernel(H!(Insert(ZeroRow, OrderNSeq[k-1], l^(b-1))));
        Append(~Fks, Fks[k-1] meet Condition);
    end for;

    One := [];

    for k in [1..#OrderNSeq] do
        OneRow := ZeroRow cat [0];
        OneRow[OrderNSeq[k]] := 1;
        OneRow[#Gen+1] := -1;
        // OneRow;
        Fks[k] := Fks[k] meet Kernel(H!OneRow);
        // F[k];
    end for;

    //QChars := [Homomorphism(Q, Zn, Gen, VectorToExps(v)) : v in Fks[k] meet ExpSpace, k in [1..#OrderNSeq] | v[OrderNSeq[k]] eq 1];

    // Construct the filtration to compute conductors
    Fil:=[ExpSpace];
    for i in [1 .. #Maps] do
        Ker:=[Q!GtoQ(g) : g in Generators(Kernel(Maps[i]))];
        V:=Fil[i];
        for g in Ker do
            phi:=H!(ElementToSequence(g) cat [0]);
            V:=V meet Kernel(phi); 
        end for;
        Fil:=Append(Fil,V);
    end for;
    
    Zn := AdditiveGroup(R);
    ZZ := Integers();

    function VectorToExps(v)
        return [Zn!ZZ!v[i] : i in [1..#Gen]];
    end function;

    Exponents := [v : v in Fks[k] meet ExpSpace, k in [1..#OrderNSeq] | v[OrderNSeq[k]] eq 1];

    QChars := [
        [*
            Homomorphism(Q, Zn, Gen, VectorToExps(v)), 
            Min([#Fil - i + 1 : i in [1..#Fil] | v in Fil[i]])
        *] : v in Exponents
    ];
    return [*[*FastMap(GtoQ*f[1]), f[2]*] : f in QChars*];
end function;

function FastCharactersOfOrder(G, Maps, n : Elements:=[], Values:=[])
    ls := Factorization(n);
    Chars := [* *];
    if not (Exponent(G) mod n eq 0) then return Chars; end if;
    Zn := AdditiveGroup(Integers(n));
    ZZ := Integers();

    for l in ls do
        lChars := FastCharactersOfPrimePowerOrder(G, Maps, l[1], l[2] : Elements:=Elements, Values:=Values);
        if #lChars eq 0 then return [* *]; end if;
        Zl := Codomain(lChars[1][1]);
        ZltoZn := hom<Zl -> Zn | Zl!1 -> Zn!(ZZ!(n/(l[1]^l[2])))>;
        if #Chars eq 0 then 
            Chars := [* [* chi[1]*ZltoZn, chi[2] *] : chi in lChars*];
        else
            Chars := [* 
                [* 
                    FastMapSum(chi[1], (psi[1]*ZltoZn)), 
                    Max(chi[2], psi[2])
                *] : chi in Chars, psi in lChars 
            *];
        end if;
    end for;
    return Chars;
end function;

function CharacterFactorsThrough(A, B, pi, chi)
    for g in Generators(Kernel(pi)) do
        if not IsIdentity(chi(g)) then
            return false;
        end if;
    end for;
    return true;
end function;

function ListValueFilter(list, val, chi, lift)
    for g in list do
        if not (chi(Inverse(lift)(g)) eq Codomain(chi)!val) then return false; end if;
    end for;
    return true;
end function;

function ComputeConductor(chi, groups, maps)
    f := #groups;
    cond := f;
    while cond gt 1 and  \
        CharacterFactorsThrough(groups[1], groups[f - cond + 2], maps[f - cond + 1], chi) do
        cond := cond - 1;
    end while;
    return cond;
end function;