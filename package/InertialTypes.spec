import "utils.m" : IsValidExceptionalExtension, FastMap;

declare type InChtr;
declare attributes InChtr:
    GrpExp,
    CondExp,
    Field,
    Lift,
    Order,
    Map
;

// print(phi);
// phi * psi;
// phi(x);



intrinsic InertiaCharacter(Order::RngIntElt, 
                                GrpExp::RngIntElt,
                                CondExp::RngIntElt,  
                                Lift::.,
                                Elements::SeqEnum[GrpAbElt], 
                                Values::SeqEnum[GrpAbElt]) -> InChtr
{Create an inertia character}
    phi := New(InChtr);
    A := Parent(Elements[1]);
    B := Parent(Values[1]);
    assert IsAbelian(B);

    assert GrpExp ge CondExp;
    phi`GrpExp := CondExp;
    phi`CondExp := CondExp;

    phi`Map := Homomorphism(A, B, Elements, Values);
    phi`Order := Order;
    phi`Lift := Lift;
    phi`Field := Codomain(Lift);

    return phi;
end intrinsic;

intrinsic '@'(x::GrpAbElt, phi::InChtr) -> GrpAbElt
{Return the image of x through the character phi}
    return phi`Map(x);
end intrinsic;

intrinsic '@'(x::RngPadElt, phi::InChtr) -> GrpAbElt
{Return the image of x through the character phi}
    return phi`Map(Inverse(phi`Lift)(x));
end intrinsic;

intrinsic '@'(x::FldPadElt, phi::InChtr) -> GrpAbElt
{Return the image of x through the character phi}
    return phi`Map(Inverse(phi`Lift)(x));
end intrinsic;

intrinsic Print(phi::InChtr)
{Print phi}
    print("Inertia Character of the field");
    print("\t"),phi`Field;
    printf "of order %o and CondExp %o", phi`Order, phi`CondExp;
end intrinsic;

function FastMapSum(f, g) 
    A:=Domain(f);
    B:=Codomain(f);
    
    Gens := [x : x in Generators(A)];
    Fmap:= Homomorphism(A, B, Gens, [f(x) + g(x) : x in Gens]);
    return Fmap;
end function;

intrinsic '*'(phi::InChtr, psi::InChtr) -> InChtr
{Return phi * psi, as long as they have coprime orders}
    assert Gcd(phi`Order, psi`Order) eq 1;
    assert phi`Field eq psi`Field;

    m := phi`Order;
    n := psi`Order;
    Zm := Codomain(phi`Map);
    Zn := Codomain(psi`Map);
    Zmn := AdditiveGroup(Integers(m*n));
    ZmtoZmn := hom<Zm -> Zmn | Zm!1 -> Zmn!n>;
    ZntoZmn := hom<Zn -> Zmn | Zn!1 -> Zmn!m>;

    product := New(InChtr);
    product`GrpExp := phi`GrpExp;
    product`Order := phi`Order * psi`Order;
    product`CondExp := Max(phi`CondExp, psi`CondExp);
    product`Map := FastMapSum(phi`Map * ZmtoZmn, psi`Map * ZntoZmn);
    product`Field := phi`Field;
    product`Lift := phi`Lift;

    return product;
end intrinsic;

intrinsic '*'(lChars::SeqEnum[InChtr], rChars::SeqEnum[InChtr]) -> SeqEnum[InChtr]
{Do all products of a character from each list}
    return [p * q : p in lChars, q in rChars];
end intrinsic;


///////////////////////////////

declare type InType;
declare attributes InType:
    BaseField,
    CondExp,
    Character,
    InField
;

intrinsic 'eq'(tau1::InType, tau2::InType) -> BoolElt
{Determines whether the two types are isomorphic 
as representations of inertia.}
// TODO: triply imprimitives
    if not Type(tau1) eq Type(tau2) then return false;
    else 
        isIsom, i := IsIsomorphic(Codomain(tau1`Character`Map), Codomain(tau2`Character`Map));
        if not isIsom then return false; end if;

        plus := true;
        minus := true;
        // TODO: fix domains
        for g in Generators(Domain(tau1`Character`Map)) do 
            plus := plus and i(tau1`Character`Map(g)) eq tau2`Character`Map(g);
            minus := minus and i(tau1`Character`Map(g)) eq -tau2`Character`Map(g);
            if not (plus or minus) then return false; end if;
        end for;
        return true;
    end if;
end intrinsic;

intrinsic 'in'(tau::InType, list::[InType]) -> BoolElt
{Returns whether tau is in list}
    for rho in list do
        if tau eq rho then
            return true; 
        end if;
    end for;
    return false;
end intrinsic;

////////////////

declare type NullInType: InType;

intrinsic IsNull(tau::InType) -> BoolElt
{Returns true if and only if tau is of type NullIT}
    return Type(tau) eq NullInType;
end intrinsic;


intrinsic Print(tau::InType)
{Print tau}
    print("Inertia Type of the field");
    print("\t"),tau`BaseField;
    printf "of conductor exponent %o\n", tau`CondExp;
    printf "with underlying character of order %o and conductor exponent %o",
        tau`Character`Order, tau`Character`CondExp;
end intrinsic;

intrinsic Print(tau::NullInType)
{Print the Null Inertia Type}
    print("NullInType");
end intrinsic;


////////////////


declare type PSInType: InType;

intrinsic PrincipalSeriesType(phi::InChtr) -> PSInType
{Create the principal series inertia type given by the character phi}
    ps := New(PSInType);
    ps`BaseField := phi`Field;
    ps`CondExp := 2 * phi`CondExp;
    ps`Character := phi;
    return ps;
end intrinsic;

intrinsic Print(tau::InType)
{Print tau}
    print("Inertia Type of the field");
    print("\t"),tau`BaseField;
    printf "of conductor exponent %o\n", tau`CondExp;
    printf "with underlying character of order %o and conductor exponent %o",
        tau`Character`Order, tau`Character`CondExp;
end intrinsic;




declare type SCUInType: InType;

intrinsic SupercuspidalUnramifiedType(phi::InChtr, F::FldPad) -> SCUInType
{Create the supercuspidal unramified inertia type of F induced by the character phi}
    assert Degree(phi`Field, F) eq 2;
    assert Valuation(Discriminant(phi`Field, F)) eq 0;

    scu := New(SCUInType);
    scu`BaseField := F;
    scu`CondExp := 2 * phi`CondExp;
    scu`Character := phi;
    return scu;
end intrinsic;


declare type SCRInType: InType;
declare attributes SCRInType:
    InducingField
;


intrinsic SupercuspidalRamifiedType(phi::InChtr, F::FldPad) -> SCRInType
{Create the supercuspidal ramified inertia type of F induced by the character phi}
    assert Degree(phi`Field, F) eq 2;

    CondExpFK := Valuation(Discriminant(phi`Field, F));
    assert CondExpFK gt 0;

    scr := New(SCRInType);
    scr`BaseField := F;
    scr`CondExp := CondExpFK + phi`CondExp;
    scr`Character := phi;
    scr`InducingField := phi`Field;

    return scr;
end intrinsic;


declare type SimplyImprInType: SCRInType;
declare type TriplyImprInType: SCRInType;
declare attributes TriplyImprInType:
    Characters,
    InducingFields,
    Indexes
;

intrinsic TriplyImprimitiveType(phis::SeqEnum[InChtr], F::FldPad) -> TriplyImprInType
{Creates a supercuspidal triply imprimitive inertia type of F induced by the tuple of characters [phi]}
    assert #phis eq 3;
    assert Degree(phis[1]`Field, F) eq 2;
    assert Degree(phis[2]`Field, F) eq 2;
    assert Degree(phis[3]`Field, F) eq 2;

    CondExpFK := [
        Valuation(Discriminant(phi`Field, F)) : phi in phis
    ];
    assert CondExpFK[1] gt 0;
    assert CondExpFK[2] gt 0;
    assert CondExpFK[3] gt 0;

    triply := New(TriplyImprInType);
    triply`BaseField := F;
    CondExps := [CondExpFK[i] + phis[i]`CondExp : i in [1..3]];
    
    assert CondExps[1] eq CondExps[2] and CondExps[2] eq CondExps[3];

    triply`Characters := phis;
    triply`CondExp := CondExps[1];
    // Assign the first character for uniformity with other InTypes
    triply`Character := phis[1];
    triply`InducingFields := [phi`Field : phi in phis];

    return triply;
end intrinsic;

intrinsic TriplyImprimitiveType(phis::SeqEnum[InChtr], F::FldPad, In::SeqEnum[RngIntElt]) -> TriplyImprInType
{Creates a supercuspidal triply imprimitive inertia type of F induced by the tuple of characters [phi]}
    tau := TriplyImprimitiveType(phis, F);
    tau`Indexes := In;

    return tau;
end intrinsic;

intrinsic TriplyImprimitiveType(phi::InChtr, F::FldPad) -> TriplyImprInType
{Creates a supercuspidal triply imprimitive inertia type of F induced by a character phi.
The two remaining characters are not computed.}
    CondExpFK := Valuation(Discriminant(phi`Field, F));
    
    assert CondExpFK gt 0;

    triply := New(TriplyImprInType);
    triply`BaseField := F;
    triply`CondExp := CondExpFK + phi`CondExp;
    triply`Character := phi;

    // The following value is assigned but should contain a list of three characters
    triply`Characters := [phi];
    // triply`Indexes := ???

    return triply;
end intrinsic;


intrinsic TriplyImprimitiveType(phi::InChtr, F::FldPad, InducingFields::SeqEnum[FldPad]) -> TriplyImprInType
{Creates a supercuspidal triply imprimitive inertia type of F induced by a character phi.
The two remaining characters are not computed.}
    CondExpFK := Valuation(Discriminant(phi`Field, F));
    
    assert CondExpFK gt 0;

    triply := New(TriplyImprInType);
    triply`BaseField := F;
    triply`CondExp := CondExpFK + phi`CondExp;
    triply`Character := phi;

    // The following value is assigned but should contain a list of three characters
    triply`Characters := [phi];
    triply`InducingFields := InducingFields;

    return triply;
end intrinsic;


intrinsic Print(tau::TriplyImprInType)
{Prints a triply imprimitive inertia type}
    print("Triply Imprimitive Inertia Type of the field");
    print("\t"),tau`BaseField;
    printf "of conductor exponent %o\n", tau`CondExp;
    if #tau`Characters eq 3 then
        printf "with 3 underlying characters of order 4 and conductor exponents [%o, %o, %o]",
            tau`Characters[1]`CondExp, tau`Characters[2]`CondExp, tau`Characters[3]`CondExp;
    else 
        printf "with an underlying character of order 4 and conductor exponent %o", 
            tau`Characters[1]`CondExp;
    end if;
end intrinsic;


declare type ExceptionalInType: InType;
declare attributes ExceptionalInType:
    TriplyField,
    Triply
;

intrinsic ExceptionalType(tau::TriplyImprInType, F::FldPad) -> ExceptionalInType
{Create the exceptional inertia type of F given by the character phi}
    L := tau`BaseField;

    assert IsValidExceptionalExtension(F, L);

    exc := New(ExceptionalInType);
    exc`BaseField := F;
    exc`TriplyField := L;
    exc`Triply := tau;

    InductionCondExp := tau`CondExp;
    RamificationLF := RamificationDegree(L,F);

    exc`CondExp := Integers()!(2 + (InductionCondExp - 2)/RamificationLF);
    exc`Character := tau`Character;

    return exc;
end intrinsic;

intrinsic ExceptionalType(phi::InChtr, F::FldPad, L::FldPad) -> ExceptionalIT
{Create the exceptional inertia type of F given by the character phi}
    return ExceptionalType(TriplyImprimitiveType(phi, L), F);
end intrinsic;

intrinsic ExceptionalType(phi::InChtr, F::FldPad, L::FldPad, InducingFields::SeqEnum[FldPad]) -> ExceptionalIT
{Create the exceptional inertia type of F given by the character phi and with given
 inducing fields for the triply imprimitive type}
    return ExceptionalType(TriplyImprimitiveType(phi, L, InducingFields), F);
end intrinsic;


intrinsic SemistabilityDefect(tau::InType) -> RngIntElt
{Returns the semistability defect of tau}
    return tau`Character`Order * RamificationDegree(tau`Character`Field, tau`BaseField);
end intrinsic;

function CharInField(chi)
    K := chi`Field;
    Cond := chi`CondExp;
    ChiLift := chi`Lift;
    // TODO: IMPLEMENT THE CORRECT BOUND
    r := chi`Order;
    prec := [Precision(K)];//[30, 60, Precision(K)];
    t := Cputime();
    for c in prec do
        try
            K2 := ChangePrecision(K,c);
            U, m := UnitGroup(K2);
            Utors := sub<U|[g : g in Generators(U)| not IsZero(Order(g))]>;
            f := Coercion(Utors,U) * m * Coercion(K2,K) * Inverse(ChiLift) * chi`Map;
            f := FastMap(f);
            break;
        catch e
            vprint InTypes : e;
        end try;
    end for;
    Norms := sub<U|Kernel(f), Inverse(m)(UniformizingElement(K2))>;
    L := ClassField(m, Norms);
    vprintf InTypes : "Computed one inertia field in %os\n", Cputime(t);
    return L, U/Norms;
end function;


intrinsic InField(tau::InType) -> FldPad
{Returns the inertia field of the type tau}
    if not assigned tau`InField then
        if (Type(tau) eq TriplyImprInType) and (#tau`InducingFields ge 2) then
            vprint InTypes : "Computing InField of triply imprimitive type";

            F := tau`BaseField;
            K1 := tau`InducingFields[1];
            K1x<x> := PolynomialRing(K1);
            E := SplittingField(x^2 - K1!(Discriminant(tau`InducingFields[2], F)));

            t := Cputime();
            E2 := ChangePrecision(E,Max(Precision(F), 60));
            UE, UEtoE := UnitGroup(E2);
            EtoUE := Inverse(UEtoE);
            Utors := sub<UE|[g : g in Generators(UE)| not IsZero(Order(g))]>;
            Utorsgens := SetToSequence(Generators(Utors));
            Utorsnorm := [Norm(UEtoE(g), K1) : g in Utorsgens];
            piE2 := EtoUE(UniformizingElement(E2));
            vprintf InTypes: "Computed Nm(M) in %os. Computing inertia field...\n", Cputime(t);

            chi := tau`Character;

            ker := Kernel(Homomorphism(Utors, Codomain(chi`Map), Utorsgens, 
                [chi(Nmg) : Nmg in Utorsnorm]
            ));
            Norms := sub<UE|ker, piE2>;
            L1 := ClassField(UEtoE, Norms);

            L1disc := Discriminant(L1, E2);
            ET<T> := PolynomialRing(E);
            L := SplittingField(T^2 - ChangePrecision(E!L1disc, Precision(E)));

            vprintf InTypes : "Computation of InField of triply imprimitive took %os\n", Cputime(t);
        elif (Type(tau) eq ExceptionalInType) then
            vprint InTypes : "Reducing InField computation to triply imprimitive type";
            L := InField(tau`Triply);
        else
            L, G := CharInField(tau`Character);
        end if;
        tau`InField := L;
    end if;

    return tau`InField;
end intrinsic;

intrinsic FindInType(L::FldPad, CandidateTypes::SeqEnum[InType]) -> .
{FindInType}
    // Warning: this function will only work if all the candidate types
    // have a character with same Field, GrpExp and Lift
    chi := CandidateTypes[1]`Character;
    K := chi`Field;
    exp := Max(chi`GrpExp, AbsoluteRamificationDegree(L) + 1);
    lift := chi`Lift;

    L1 := ChangePrecision(L, exp);
    OL := Integers(L1);
    UL, ULtoOL := UnitGroup(OL);
    Gen := [g : g in Generators(UL)];
    Norms:=[Inverse(lift)(Norm(ChangePrecision(L!L1!ULtoOL(g),Precision(L)),K)): g in Gen];
    i :=1;
    for tau in CandidateTypes do
        found := true;
        for g in Norms do
            if not IsIdentity(tau`Character(g)) then
                found := false;
                break;
            end if;
        end for;
        if found then return tau, i; end if;
        i +:=1;
    end for;
    return New(NullInType), 0;
end intrinsic;