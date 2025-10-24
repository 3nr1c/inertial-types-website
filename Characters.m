function TupleToSeq(t)
    return [x : x in t];
end function;

function CharactersOfOrder(G, n)
    ZZ := Integers();
    Zn := AdditiveGroup(Integers(n));

    Q, GtoQ := quo<G | [ZZ!(Gcd(Order(g),n)) * g : g in Generators(G)]>;

    GZn, t := Hom(Q, Zn);
    QChars := {};
    for f in GZn do
        if not (-f in QChars) and Order(f) eq n then
            Include(~QChars, f);
        end if;
    end for;

    return [FastMap(GtoQ*(t(f))) : f in QChars];
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

function FastCharactersOfOrder(G, n)
    if not (n in {2, 3, 4}) then
        return CharactersOfOrder(G, n);
    end if;

    ZZ := Integers();
    Zn := AdditiveGroup(Integers(n));
    Q, GtoQ := quo<G | [ZZ!(Gcd(Order(g),n)) * g : g in Generators(G)]>;
    Q;
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
                < {Zn!t : t in [0 .. n by Order(g)]} : g in GensOfLowerOrder >
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

    return [*FastMap(GtoQ*f) : f in QChars*];
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