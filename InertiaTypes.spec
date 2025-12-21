declare type InertiaCharacter;
declare attributes InertiaCharacter:
    CondExp,
    Field,
    Lift,
    Order,
    Map
;

intrinsic NewInertiaCharacter(Order::RngIntElt, 
                                CondExp::RngIntElt,  
                                Lift::.,
                                Elements::SeqEnum[GrpAbElt], 
                                Values::SeqEnum[GrpAbElt]) -> InertiaCharacter
{Create an inertia character}
    phi := New(InertiaCharacter);
    A := Parent(Elements[1]);
    B := Parent(Values[1]);
    assert IsAbelian(B);

    phi`Map := Homomorphism(A, B, Elements, Values);
    phi`Order := Order;
    phi`CondExp := CondExp;
    phi`Lift := Lift;
    phi`Field := Codomain(Lift);

    return phi;
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

intrinsic Print(tau::InertiaType)
{Print tau}
    print("Inertia Character of the field");
    print("\t"),tau`BaseField;
    printf "of CondExp exponent %o\n", tau`CondExp;
    printf "with underlying character of order %o and CondExp exponent %o",
        tau`Character`Order, tau`Character`CondExp;
end intrinsic;


declare type PrincipalSeriesIT: InertiaType;
declare attributes PrincipalSeriesIT: Character;

intrinsic NewPrincipalSeriesIT(phi::InertiaCharacter) -> PrincipalSeriesIT
{Create the principal series inertia type given by the character phi}
    ps := New(PrincipalSeriesIT);
    ps`BaseField := phi`Field;
    ps`CondExp := 2 * phi`CondExp;
    ps`Character := phi;
    return ps;
end intrinsic;


declare type SupercuspidalUnramifiedIT: InertiaType;
declare attributes SupercuspidalUnramifiedIT: Character;

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
    InducingField,
    Character
;

intrinsic NewSupercuspidalRamifiedIT(phi::InertiaCharacter, F::FldPad) -> SupercuspidalRamifiedIT
{Create the (simply imprimitive) supercuspidal ramified inertia 
    type of F induced by the character phi}
    assert Degree(phi`Field, F) eq 2;

    CondExpFK := Valuation(Discriminant(phi`Field, F));
    assert CondExpFK gt 0;

    scr := New(SupercuspidalRamifiedIT);
    scr`BaseField := F;
    scr`CondExp := CondExpFK + phi`CondExp;
    scr`Character := phi;

    return scr;
end intrinsic;

declare type TriplyImprimitiveIT: InertiaType;
declare attributes TriplyImprimitiveIT:
    InducingFields,
    Characters
;