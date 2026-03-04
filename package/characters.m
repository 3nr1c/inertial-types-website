function FastCharactersOfPrimePowerOrder(G, l, b, Maps, lift: Elements:=[], Values:=[])
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

    Chars := [];
    for v in Exponents do
        CondExp := Min([#Fil - i + 1 : i in [1..#Fil] | v in Fil[i]]);

        phi := InertiaCharacter(n, #Fil, CondExp, lift, Gen, VectorToExps(v));
        phi`Map := GtoQ * phi`Map;

        Append(~Chars, phi);
    end for;

    return Chars;
end function;

function FastCharactersOfOrder(G, n, Maps, lift : Elements:=[], Values:=[])
    ls := Factorization(n);
    Chars := [];
    if not (Exponent(G) mod n eq 0) then return Chars; end if;

    for l in ls do
        rChars := FastCharactersOfPrimePowerOrder(G, l[1], l[2], Maps, lift : Elements:=Elements, Values:=Values);
        if #rChars eq 0 then return [];
        elif #Chars eq 0 then 
            Chars := rChars;
        else
            Chars *:= rChars;
        end if;
    end for;
    return Chars;
end function;
