declare type InertiaCharacter;
declare attributes InertiaCharacter:
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

intrinsic NewInertiaCharacter(Order::RngIntElt, 
                                GrpExp::RngIntElt,
                                CondExp::RngIntElt,  
                                Lift::.,
                                Elements::SeqEnum[GrpAbElt], 
                                Values::SeqEnum[GrpAbElt]) -> InertiaCharacter
{Create an inertia character}
    phi := New(InertiaCharacter);
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

intrinsic '@'(x::., phi::InertiaCharacter) -> .
{Return the image of x through the character phi}
    return phi`Map(x);
end intrinsic;

intrinsic Print(phi::InertiaCharacter)
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

intrinsic '*'(phi::InertiaCharacter, psi::InertiaCharacter) -> InertiaCharacter
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

    product := New(InertiaCharacter);
    product`GrpExp := phi`GrpExp;
    product`Order := phi`Order * psi`Order;
    product`CondExp := Max(phi`CondExp, psi`CondExp);
    product`Map := FastMapSum(phi`Map * ZmtoZmn, psi`Map * ZntoZmn);
    product`Field := phi`Field;
    product`Lift := phi`Lift;

    return product;
end intrinsic;

intrinsic '*'(lChars::SeqEnum[InertiaCharacter], rChars::SeqEnum[InertiaCharacter]) -> SeqEnum[InertiaCharacter]
{Do all products of a character from each list}
    return [p * q : p in lChars, q in rChars];
end intrinsic;


///////////////////////////////

declare type InertiaType;
declare attributes InertiaType:
    BaseField,
    CondExp,
    Character
;

intrinsic 'eq'(tau1::InertiaType, tau2::InertiaType) -> BoolElt
{Determines whether the two types are isomorphic 
as representations of inertia.}
// TODO: triply imprimitives
    if not Type(tau1) eq Type(tau2) then return false;
    else 
        isIsom, i := IsIsomorphic(Codomain(tau1`Character`Map), Codomain(tau2`Character`Map));
        if not isIsom then return false; end if;

        plus := true;
        minus := true;
        for g in Generators(Domain(tau1`Character`Map)) do 
            plus := plus and i(tau1`Character`Map(g)) eq tau2`Character`Map(g);
            minus := minus and i(tau1`Character`Map(g)) eq -tau2`Character`Map(g);
            if not (plus or minus) then return false; end if;
        end for;
        return true;
    end if;
end intrinsic;

intrinsic 'in'(tau::InertiaType, list::[InertiaType]) -> BoolElt
{Returns whether tau is in list}
    for rho in list do
        if tau eq rho then
            return true; 
        end if;
    end for;
    return false;
end intrinsic;

////////////////

declare type NullIT: InertiaType;

intrinsic IsNull(tau::InertiaType) -> BoolElt
{Returns true if and only if tau is of type NullIT}
    return Type(tau) eq NullIT;
end intrinsic;


intrinsic Print(tau::InertiaType)
{Print tau}
    print("Inertia Type of the field");
    print("\t"),tau`BaseField;
    printf "of conductor exponent %o\n", tau`CondExp;
    printf "with underlying character of order %o and conductor exponent %o",
        tau`Character`Order, tau`Character`CondExp;
end intrinsic;

intrinsic Print(tau::NullIT)
{Print the Null Inertia Type}
    print("NullIT");
end intrinsic;


////////////////


declare type PrincipalSeriesIT: InertiaType;

intrinsic NewPrincipalSeriesIT(phi::InertiaCharacter) -> PrincipalSeriesIT
{Create the principal series inertia type given by the character phi}
    ps := New(PrincipalSeriesIT);
    ps`BaseField := phi`Field;
    ps`CondExp := 2 * phi`CondExp;
    ps`Character := phi;
    return ps;
end intrinsic;

intrinsic Print(tau::InertiaType)
{Print tau}
    print("Inertia Type of the field");
    print("\t"),tau`BaseField;
    printf "of conductor exponent %o\n", tau`CondExp;
    printf "with underlying character of order %o and conductor exponent %o",
        tau`Character`Order, tau`Character`CondExp;
end intrinsic;




declare type SupercuspidalUnramifiedIT: InertiaType;

intrinsic NewSupercuspidalUnramifiedIT(phi::InertiaCharacter, F::FldPad) -> SupercuspidalUnramifiedIT
{Create the supercuspidal unramified inertia type of F induced by the character phi}
    assert Degree(phi`Field, F) eq 2;
    assert Valuation(Discriminant(phi`Field, F)) eq 0;

    scu := New(SupercuspidalUnramifiedIT);
    scu`BaseField := F;
    scu`CondExp := 2 * phi`CondExp;
    scu`Character := phi;
    return scu;
end intrinsic;


declare type SupercuspidalRamifiedIT: InertiaType;
declare attributes SupercuspidalRamifiedIT:
    InducingField
;

// declare type SimplyImprimitiveIT: SupercuspidalRamifiedIT;
// declare type TriplyImprimitiveIT: SupercuspidalRamifiedIT;
// declare attributes TriplyImprimitiveIT:
//     Characters
// ;

intrinsic NewSupercuspidalRamifiedIT(phi::InertiaCharacter, F::FldPad) -> SupercuspidalRamifiedIT
{Create the supercuspidal ramified inertia type of F induced by the character phi}
    assert Degree(phi`Field, F) eq 2;

    CondExpFK := Valuation(Discriminant(phi`Field, F));
    assert CondExpFK gt 0;

    scr := New(SupercuspidalRamifiedIT);
    scr`BaseField := F;
    scr`CondExp := CondExpFK + phi`CondExp;
    scr`Character := phi;
    scr`InducingField := phi`Field;

    return scr;
end intrinsic;

// intrinsic GetTripleOfCharacters(tau::SupercuspidalRamifiedIT) -> [Character]
//     assert in_deg(tau`BaseField) % 2 eq 0;
//     // code
//     return [phi1,phi2,phi3];
// end intrinsic;

declare type ExceptionalIT: InertiaType;
declare attributes ExceptionalIT:
    CubicField
;


intrinsic NewExceptionalIT(phi::InertiaCharacter, F::FldPad, L::FldPad) -> ExceptionalIT
{Create the exceptional inertia type of F given by the character phi}
    assert Degree(L, F) eq 3;

    CondExpFK := Valuation(Discriminant(phi`Field, F));
    assert CondExpFK gt 0;

    exc := New(ExceptionalIT);
    exc`BaseField := F;

    InductionCondExp := phi`CondExp + Valuation(Discriminant(phi`Field, L));
    RamificationLF := RamificationDegree(L,F);


    exc`CondExp := Integers()!(2 + (InductionCondExp - 2)/RamificationLF);
    exc`Character := phi;
    exc`CubicField := L;

    return exc;
end intrinsic;

intrinsic SemistabilityDefect(tau::InertiaType) -> RngIntElt
{Returns the semistability defect of tau}
    if Type(tau) eq PrincipalSeriesIT then
        return tau`Character`order;
    elif Type(tau) eq SupercuspidalUnramifiedIT then
        return tau`Character`order;
    elif Type(tau) eq SupercuspidalRamifiedIT then
        return -1;
    elif Type(tau) eq ExceptionalIT then
        if (AbsoluteInertiaDegree(tau`Field) mod 2) eq 0 then
            return 8;
        else
            return 24;
        end if;
    end if;
end intrinsic;