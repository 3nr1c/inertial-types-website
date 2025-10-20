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

function AffinePoints(k, G)
// return all points in A_k(G)
    if k le 0 then 
        points := [];
    elif k eq 1 then
        points := [[i] : i in G];
    else// k gt 2
        points_kminus1 := AffinePoints(k - 1, G);
        points := [[i] cat p : i in G, p in points_kminus1];
    end if;

    return points;
end function;

function CharacterExponents(k, Zn : HalfZn := {})
// This function returns the tuples (x1,...,xj)
// necessary to obtain all characters of exact order n,
// modulo -1
    if k le 0 then
        tuples := [];
    elif k eq 1 then
        tuples := [[Zn!1]];
    else
        if #HalfZn eq 0 then
            HalfZn := {Zn!1};
            for g in Zn do
                if not (-g in HalfZn) then
                    Include(~HalfZn, g);
                end if;
            end for;
            Exclude(~HalfZn, Zn!1);
        end if;

        TupleToList := func<t | [e : e in t]>;
        tuples := {[Zn!1] cat TupleToList(p) : p in CartesianPower(Zn, k - 1)};
        Exponentskminus1 := CharacterExponents(k - 1, Zn : HalfZn:=HalfZn);
        for g in HalfZn do
            tuples := tuples join {[g] cat p : p in Exponentskminus1};
        end for;
    end if;
    return tuples;
end function;

function FastCharactersOfOrder(G, n)
    if not (n in {2, 3, 4}) then
        return CharactersOfOrder(G, n);
    end if;

    ZZ := Integers();
    Zn := AdditiveGroup(Integers(n));
    Q, GtoQ := quo<G | [ZZ!(Gcd(Order(g),n)) * g : g in Generators(G)]>;
    GensOfOrder_n := [g : g in Generators(Q) | Order(g) eq n];
    GensOfLowerOrder := [g : g in Generators(Q) | Order(g) lt n];
    Gens := GensOfOrder_n cat GensOfLowerOrder;

    QChars := [* *];

    for e1 in CharacterExponents(#GensOfOrder_n, Zn) do
        if #GensOfLowerOrder gt 0 then
            // The following needs to be changed if we want to 
            // compute fast characters for composite n distinct from 4:
            LowerOrderImages := {Zn!0, Zn!2};
            // In general, one should order the GensOfLowerOrder, then
            // build a cartesian product (not a power) with the possible
            // exponents for each generator. This is necessary in order to
            // avoid repetition.

            for e2 in CartesianPower(LowerOrderImages, #GensOfLowerOrder) do
                Append(~QChars, Homomorphism(Q, Zn, Gens, e1 cat [t : t in e2]));
            end for;
        else
            Append(~QChars, Homomorphism(Q, Zn, Gens, e1));
        end if;
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