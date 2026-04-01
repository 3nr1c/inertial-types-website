// load "inertial-types3.m";

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
    ExGroups:=[* *];
    ExLifts:=[* *];
    ExExp:=[* *];
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
        VarepsGenerators := [K1!llift(g) : g in Generators(G)];

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

        
        Uf,UpStairsUf:=OptimalNorms(E,K1,#CGroups1);
        Uf1:=[Inverse(CLift1)(g): g in Uf];
        muUf1:=[Inverse(CLift1)(Norm(mu(g),K1)): g in UpStairsUf];
        


        Elements := Elements cat [2*g : g in Uf1];
        Values := Values cat [0 : i in [1 .. #Uf1]];

        //Elements2:=Elements cat [Uf1[i] + muUf1[i] : i in [1 .. #Uf1]];

        Elements := Elements cat [Uf1[i] - muUf1[i] : i in [1 .. #Uf1]];
        Values := Values cat [0 : i in [1 .. #Uf1]];

        Caracteres:=FastCharactersOfPrimePowerOrder(CGroups1[1], 2, 2, CMaps1, CLift1 : Elements:=Elements, Values:=Values);

        if not IsEmpty(Caracteres) then 
            Append(~ExceptionalChars,[
                NewExceptionalIT(phi, F, L) : phi in Caracteres
            ]);
            ExGroups:=Append(ExGroups,CGroups1[1]);
            ExLifts:=Append(ExLifts,CLift1);
            ExExp:=Append(ExExp,#CGroups1);
            // Domain(CLift1) eq Domain(Caracteres[1]`Map);
        end if;
    end for;

    return ExceptionalChars;
end function;


function ExceptionalTypesSimply(Fi)
   
    Fix<x>:=PolynomialRing(Fi);
    F:=UnramifiedExtension(Fi,2);
    for l in [1..3] do 
        L:=FieldOfFractions(AllExtensions(F,3)[l]);
        if IsNormal(L,Fi) then break; end if;
    end for;

    //F<zeta3>:=ext<Fi|x^2+x+1>;
    //R<x>:=PolynomialRing(F);
    //L:=ext<F|x^3-UniformizingElement(F)>;
    assert Degree(F,Fi) eq 2; 
    assert RamificationDegree(F,Fi) eq 1;
    assert RamificationDegree(L,Fi) eq 3;
    assert IsNormal(L,Fi);
    // for l in [1..3] do
    //     L:=FieldOfFractions(AllExtensions(F,3)[l]);
    //     if IsNormal(L, Fi) and RamificationDegree(L,Fi) eq 3 then break; end if;
    // end for;

    R<X> := PolynomialRing(L);
    GSel, Sel, SeltoL, Gal, GaltoAut := SelmerGaloisModule(Fi,L);
    //sigma := GaltoAut(Gal.2);

    // We'll probably remove this
    for tau in Gal do
        if Order(tau) eq 3 then rho := GaltoAut(tau); break; end if;
    end for;
    for tau in Gal do
        if Order(tau) eq 2 then sigma := GaltoAut(tau); break; end if;
    end for;

    SelOrbits := [M: M in MinimalSubmodules(GSel) | Dimension(M) eq 2];
    ExceptionalChars:=[* *];
    ExGroups:=[* *];
    ExLifts:=[* *];
    ExExp:=[* *];
    printf "%o Selmer orbits\n", #SelOrbits;
    for orbit in SelOrbits do
        Polynomials := [];
        roots := [];
        g:=GaltoAut(Gal.1);
        assert(IsIdentity(Gal.1));
        for i in [1..3] do
            g:=g*rho;
            z := g(ChangePrecision(SeltoL(Sel!ElementToSequence(GSel!orbit.1)), Precision(L)));
            Append(~Polynomials, X^2 - R!z);
        end for;
        K1:=SplittingField(Polynomials[1]);

        K1X<x>:=PolynomialRing(K1);
        E:=SplittingField(K1X!Polynomials[2]);

        // Initialize character conditions
        p, ram_deg, in_deg, pi, N := BaseValues(L);
        Cond, pi, Gal_L_K1, y := ExtValues(L,K1);
        f := Max(N-Cond, 2*Cond);// CHECK THE VALUE OF f HERE
        c := Cond;

        UGroups, UMaps, ULift := UComplex(L, f);
        G := UGroups[1];
        llift:=ULift;
        VarepsGenerators := [K1!llift(g) : g in Generators(G)];

        CGroups1, CMaps1, CLift1 := ConComplex(L, K1, f);
        proj := Inverse(CLift1);
        bar_y2 := 2*proj(y);

        Elements := [proj(g) : g in VarepsGenerators | not IsIdentity(proj(g))];
        Values := [2 : g in VarepsGenerators | not IsIdentity(proj(g))];
        
        // We are computing triply imprimitive => bar_y2 goes to 0
        Append(~Elements, bar_y2);
        Append(~Values, 0);

        GalE,GalEtoAut:=AutomorphismGroup(E,Fi);
        if RamificationDegree(E,F) eq 12 and IsIsomorphic(GalE,Sym(4))  then

            Uf,UpStairsUf:=OptimalNorms(E,K1,#CGroups1);

            Uf1:=[Inverse(CLift1)(g): g in Uf];
            Elements := Elements cat [2*g : g in Uf1];
            Values := Values cat [0 : i in [1 .. #Uf1]];

            for tau in GalE do
                if IsIdentity(tau) then continue; end if;
                mu:=GalEtoAut(tau);
                muUf1:=[Inverse(CLift1)(Norm(mu(g),K1)): g in UpStairsUf];
                Elements := Elements cat [Uf1[i] - muUf1[i] : i in [1 .. #Uf1]];
                Values := Values cat [0 : i in [1 .. #Uf1]];
            end for;    
            
            Caracteres:=FastCharactersOfPrimePowerOrder(CGroups1[1], 2, 2, CMaps1, CLift1 : Elements:=Elements, Values:=Values);

            if not IsEmpty(Caracteres) then 
                Append(~ExceptionalChars,[
                    NewExceptionalIT(phi, F, L) : phi in Caracteres
                ]);
                ExGroups:=Append(ExGroups,CGroups1[1]);
                ExLifts:=Append(ExLifts,CLift1);
                ExExp:=Append(ExExp,#CGroups1);
                Domain(CLift1) eq Domain(Caracteres[1]`Map);
            end if;
            print("------------------");
        end if;
         end for;
    return ExceptionalChars;
end function;


intrinsic ExceptionalTypes(F, L)
    require IsNormal(L,F) : "The extension L/F must be normal";
    require ((AbsoluteInertiaDegree(F) mod 2 eq 0) and (Degree(L, F) eq 3)) 
        or (
            (AbsoluteInertiaDegree(F) mod 2 eq 1) 
            and (Degree(L, F) eq 6) 
            and (InertiaDegree(L, F) mod 2 eq 0)
        ) : "Invalid degree conditions for L/F";

    R<X> := PolynomialRing(L);
    GSel, Sel, SeltoL, Gal, GaltoAut := SelmerGaloisModule(Fi,L);

    // Look for an element rho of order 3 in the Galois group
    for tau in Gal do
        if Order(tau) eq 3 then rho := GaltoAut(tau); break; end if;
    end for;

    SelOrbits := [M: M in MinimalSubmodules(GSel) | Dimension(M) eq 2];
    vprintf InTypes : "%o Selmer orbits\n", #SelOrbits;
    for orbit in SelOrbits do
        Polynomials := [];
        roots := [];
        g := GaltoAut(Identity(Gal));
        for i in [1..3] do
            g := g*rho;
            z := g(ChangePrecision(SeltoL(Sel!ElementToSequence(GSel!orbit.1)), Precision(L)));
            Append(~Polynomials, X^2 - R!z);
        end for;
        K1 := SplittingField(Polynomials[1]);

        K1X<x> := PolynomialRing(K1);
        E := SplittingField(K1X!Polynomials[2]);

        // The orbit will only give exceptional types if either
        // (a) L/F is cubic, or
        // (b) E/F has ramification degree 12 and is Galois with group S4
        validOrbit := Degree(L,F) eq 3;
        if not validOrbit then
            GalE,GalEtoAut:=AutomorphismGroup(E,Fi);
            validOrbit := RamificationDegree(E,F) eq 12 and IsIsomorphic(GalE,Sym(4));
        end if;

        if validOrbit then
            // Initialize character conditions
            p, ram_deg, in_deg, pi, N := BaseValues(L);
            Cond, pi, Gal_L_K1, y := ExtValues(L,K1);
            f := Max(N-Cond, 2*Cond);
            c := Cond;

            UGroups, UMaps, ULift := UComplex(L, f);
            G := UGroups[1];
            llift:=ULift;
            VarepsGenerators := [K1!llift(g) : g in Generators(G)];

            CGroups1, CMaps1, CLift1 := ConComplex(L, K1, f);
            proj := Inverse(CLift1);
            bar_y2 := 2*proj(y);

            Elements := [proj(g) : g in VarepsGenerators | not IsIdentity(proj(g))];
            Values := [2 : g in VarepsGenerators | not IsIdentity(proj(g))];
            
            // We are computing triply imprimitive => bar_y2 goes to 0
            Append(~Elements, bar_y2);
            Append(~Values, 0);

            Uf,UpStairsUf:=OptimalNorms(E,K1,#CGroups1);

            Uf1:=[Inverse(CLift1)(g): g in Uf];
            Elements := Elements cat [2*g : g in Uf1];
            Values := Values cat [0 : i in [1 .. #Uf1]];

            for tau in GalE do
                if IsIdentity(tau) then continue; end if;
                mu:=GalEtoAut(tau);
                muUf1:=[Inverse(CLift1)(Norm(mu(g),K1)): g in UpStairsUf];
                Elements := Elements cat [Uf1[i] - muUf1[i] : i in [1 .. #Uf1]];
                Values := Values cat [0 : i in [1 .. #Uf1]];
            end for;    
            
            characters := FastCharactersOfPrimePowerOrder(
                CGroups1[1], 2, 2, CMaps1, CLift1 : Elements:=Elements, Values:=Values
            );

            typesFromOrbit := [ExceptionalType(phi, F, L) : phi in Caracteres];


            if not IsEmpty(characters) then 
                Append(~ExceptionalChars, typesFromOrbit);
            end if;
            // print("------------------");
        end if;
         end for;
    return ExceptionalChars;
end intrinsic;