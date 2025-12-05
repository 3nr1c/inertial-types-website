load "inertial-types3.m";

//This function produces the 2-Selmer Group of L as a Gal(L/F) module
function SelmerGaloisModule (F,L)
    assert IsNormal(L,F);
    F2 := GF(2);
    Gal,GaltoAut := AutomorphismGroup(L,F);
    Sel,LtoSel := pSelmerGroup(2,L);
    n := #Generators(Sel);
    Operators := [ScalarMatrix(GF(2),n,1)];
    ListOfGens := [Sel.i : i in [1 .. n]];

    for t in Generators(Gal) do
        M := [];
        g := GaltoAut(t);

        for z in ListOfGens do
            y := ChangePrecision(Inverse(LtoSel)(z), Precision(L));
            Append(~M, ElementToSequence(LtoSel(g(y))));
        end for;
        Append(~Operators, Matrix(F2,M));
    end for;
    GSel := GModule(Gal, Operators);
    return GSel, Sel, Inverse(LtoSel), Gal, GaltoAut;
end function;

function ExceptionalTypesTriply(F,L)
    assert Degree(L,F) eq 3;
    R<X> := PolynomialRing(L);
    GSel, Sel, SeltoL, Gal, GaltoAut := SelmerGaloisModule(F,L);
    sigma := GaltoAut(Gal.2);
    //p, ram_deg, in_deg, pi, N := BaseValues(L);
    //ff := Floor(N/2);
    //UGroups, UMaps, ULift := UComplex(L, ff);

    SelOrbits := [M: M in MinimalSubmodules(GSel) | Dimension(M) eq 2];
    ExceptionalChars:=[* *];
    for orbit in SelOrbits do
        Polynomials := [];
        roots := [];
        for i in [1..3] do
            g:=GaltoAut(Gal.2^i);
            z := g(ChangePrecision(SeltoL(Sel!ElementToSequence(GSel!orbit.1)), Precision(L)));
            Append(~Polynomials, X^2 - z);
        end for;
        K1:=SplittingField(Polynomials[1]);
        y1:=Roots(PolynomialRing(K1)!Polynomials[1])[1,1];
        K2:=SplittingField(Polynomials[2]);
        y2:=Roots(PolynomialRing(K2)!Polynomials[2])[1,1];
        K3:=SplittingField(Polynomials[3]);
        y3:=Roots(PolynomialRing(K3)!Polynomials[3])[1,1];
        assert sigma(y1^2) eq y2^2 and sigma(y2^2) eq y3^2;

        K1X<x>:=PolynomialRing(K1);
        E:=SplittingField(K1X!Polynomials[2]);
        y1:=Roots(PolynomialRing(E)!Polynomials[1])[1,1];
        y2:=Roots(PolynomialRing(E)!Polynomials[2])[1,1];

        // Initialize character conditions
        p, ram_deg, in_deg, pi, N := BaseValues(L);
        Cond, pi, Gal_L_K1, y := ExtValues(L,K1);
        f := Max(N-Cond, 2*Cond);
        c := Cond;

        UGroups, UMaps, ULift := UComplex(L, f);
        G := UGroups[f - c + 1];
        if f - c + 1 eq 1 then
            llift := ULift;
        else
            llift := Inverse(UMaps[f - c]) * ULift;
        end if;
        VarepsGenerators := {K1!llift(g) : g in Generators(G)};

        CGroups1, CMaps1, CLift1 := ConComplex(L, K1, f);
        proj := Inverse(CLift1);
        bar_y2 := 2*proj(y);

        Elements := [proj(g) : g in VarepsGenerators | not IsIdentity(proj(g))];
        Values := [2 : g in VarepsGenerators | not IsIdentity(proj(g))];
        
        // We are computing triply imprimitive => bar_y2 goes to 0
        Append(~Elements, bar_y2);
        Append(~Values, 0);

        //Chars1,CGroups1,CMaps1,CLift1:=SupercuspidalRamified2args(L,K1);
        //FilChars1:=Chars1;
        //FilChars2:=Chars2;
        
        GalE,GalEtoAut:=AutomorphismGroup(E,F);
        for tau in GalE do
            if IsZero((GalEtoAut(tau)(y1)-y2)) then mu:=GalEtoAut(tau); break; end if;
        end for;

        E1:=ChangePrecision(E,#CGroups1);
        OE:=Integers(E1);
        UE,UEtoOE:=UnitGroup(OE);
        Gen:=[g : g in Generators(UE)];

        Uf1:=[Inverse(CLift1)(Norm(ChangePrecision(E!E1!UEtoOE(g),Precision(E)),K1)): g in Gen];
        muUf1:=[Inverse(CLift1)(Norm(ChangePrecision(mu(E!E1!UEtoOE(g)),Precision(E)),K1)): g in Gen];
        //Uf2:=[Inverse(CLift2)(Norm(ChangePrecision(E!E1!UEtoOE(g),Precision(E)),K2)): g in Generators(UE)];
        //SigUf:=[Inverse(CLift2)(ExtendAutomorphism(sigma,K1,K2,y1,y2,CLift1(g))) : g in Uf1];

        Elements := Elements cat [2*g : g in Uf1];
        Values := Values cat [0 : i in [1 .. #Uf1]];

        Elements := Elements cat [Uf1[i] - muUf1[i] : i in [1 .. #Uf1]];
        Values := Values cat [0 : i in [1 .. #Uf1]];

        time ExceptionalChars:=Append(ExceptionalChars,
            FastCharactersOfOrder4(CGroups1[1] : Elements:=Elements, Values:=Values)
        );
    end for;
    return ExceptionalChars;
end function;


function ExceptionalTypesSimply(Fi,l)
   
    Fix<x>:=PolynomialRing(Fi);
    F<zeta3>:=ext<Fi|x^2+x+1>;
    L:=FieldOfFractions(AllExtensions(F,3)[l]);
    R<X> := PolynomialRing(L);
    GSel, Sel, SeltoL, Gal, GaltoAut := SelmerGaloisModule(F,L);
    sigma := GaltoAut(Gal.2);
    SelOrbits := [M: M in MinimalSubmodules(GSel) | Dimension(M) eq 2];
    ExceptionalChars:=[* *];
    #SelOrbits;
    for orbit in SelOrbits do
        Polynomials := [];
        roots := [];
        for i in [1..3] do
            g:=GaltoAut(Gal.2^i);
            z := g(ChangePrecision(SeltoL(Sel!ElementToSequence(GSel!orbit.1)), Precision(L)));
            Append(~Polynomials, X^2 - z);
        end for;
        K1:=SplittingField(Polynomials[1]);
        y1:=Roots(PolynomialRing(K1)!Polynomials[1])[1,1];
        K2:=SplittingField(Polynomials[2]);
        y2:=Roots(PolynomialRing(K2)!Polynomials[2])[1,1];
        K3:=SplittingField(Polynomials[3]);
        y3:=Roots(PolynomialRing(K3)!Polynomials[3])[1,1];
        assert sigma(y1^2) eq y2^2 and sigma(y2^2) eq y3^2;

        K1X<x>:=PolynomialRing(K1);
        E:=SplittingField(K1X!Polynomials[2]);
        y1:=Roots(PolynomialRing(E)!Polynomials[1])[1,1];
        y2:=Roots(PolynomialRing(E)!Polynomials[2])[1,1];

        // Initialize character conditions
        p, ram_deg, in_deg, pi, N := BaseValues(L);
        Cond, pi, Gal_L_K1, y := ExtValues(L,K1);
        f := Max(N-Cond, 2*Cond);
        c := Cond;

        UGroups, UMaps, ULift := UComplex(L, f);
        G := UGroups[f - c + 1];
        if f - c + 1 eq 1 then
            llift := ULift;
        else
            llift := Inverse(UMaps[f - c]) * ULift;
        end if;
        VarepsGenerators := {K1!llift(g) : g in Generators(G)};

        CGroups1, CMaps1, CLift1 := ConComplex(L, K1, f);
        proj := Inverse(CLift1);
        bar_y2 := 2*proj(y);

        Elements := [proj(g) : g in VarepsGenerators | not IsIdentity(proj(g))];
        Values := [2 : g in VarepsGenerators | not IsIdentity(proj(g))];
        
        // We are computing triply imprimitive => bar_y2 goes to 0
        Append(~Elements, bar_y2);
        Append(~Values, 0);

        ////////////////////////
        
        time GalE,GalEtoAut:=AutomorphismGroup(E,Fi);
        #GalE;
        if #GalE eq Degree(E,Fi) then   
            for tau in GalE do
                if IsZero((GalEtoAut(tau)(y1)-y2)) and IsZero((GalEtoAut(tau)(zeta3)-zeta3)) then mu:=GalEtoAut(tau); break; end if;
            end for;
            for tau in GalE do
                if IsZero((GalEtoAut(tau)(zeta3)-zeta3^2)) then delta:=GalEtoAut(tau); break; end if; 
            end for;

            E1:=ChangePrecision(E,#CGroups1);
            OE:=Integers(E1);
            UE,UEtoOE:=UnitGroup(OE);
            Gen:=[g : g in Generators(UE)];

            Uf1:=[Inverse(CLift1)(Norm(ChangePrecision(E!E1!UEtoOE(g),Precision(E)),K1)): g in Gen];
            muUf1:=[Inverse(CLift1)(Norm(ChangePrecision(mu(E!E1!UEtoOE(g)),Precision(E)),K1)): g in Gen];
            muUf2:=[Inverse(CLift1)(Norm(ChangePrecision(delta(E!E1!UEtoOE(g)),Precision(E)),K1)): g in Gen];
            
            Elements := Elements cat [2*g : g in Uf1];
            Values := Values cat [0 : i in [1 .. #Uf1]];

            Elements := Elements cat [Uf1[i] - muUf1[i] : i in [1 .. #Uf1]];
            Values := Values cat [0 : i in [1 .. #Uf1]];

            Elements := Elements cat [Uf1[i] - muUf2[i] : i in [1 .. #Uf1]];
            Values := Values cat [0 : i in [1 .. #Uf1]];
            
            time ExceptionalChars:=Append(ExceptionalChars,
                FastCharactersOfOrder4(CGroups1[1] : Elements:=Elements, Values:=Values)
            );
            #(ExceptionalChars[#ExceptionalChars]);
            print("------------------");
        end if;
    end for;
    return ExceptionalChars;
end function;