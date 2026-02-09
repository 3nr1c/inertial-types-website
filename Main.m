load "Exceptionals.m";

function MatchTriplys (F,SCR,Twist)
    F;
    Sel,FtoSel := pSelmerGroup(2,F);
    SeltoF := Inverse(FtoSel);
    Triples:={};
    for i,j in [1..#Twist] do
        if i eq j then continue; end if; 
        x:=FtoSel(Twist[i]);
        y:=FtoSel(Twist[j]);
        z:=x*y;
        k:=[l : l in [1..#Twist]| FtoSel(Twist[l]) eq z ][1];
        if IsEmpty({tau`CondExp: tau in SCR[i]} meet {tau`CondExp: tau in SCR[j]} meet {tau`CondExp: tau in SCR[k]}) then continue; end if;
        trip:={i,j,k};
        if #trip eq 3 and not trip in Triples then Triples:=Include(Triples,trip); end if;
    end for;

    // for l in [1..#SCR] do
    //     for triply in Triples do
    //         if l in triply then
    //         i,j,k:=Explode(SetToSequence(triply));
        
    //         Ki:=SCR[i,1]`Char`Field;
    //         Ri<X>:=PolynomialRing(Ki);
    //         Ei:=SplittingField(X^2-Twist[j]);
            
    //         c:=Max([tau`Character`CondExp: tau in SCR[i]]);
    //         Uf,UpStairsUf:=OptimalNorms(Ei,Ki,c);


    //         Kj:=SCR[j,1]`Char`Field;
    //         Rj<X>:=PolynomialRing(Kj);
    //         Ej:=SplittingField(X^2-Twist[i]);

            
    //         Ki:=SCR[i,1]`Char`Field;
    //         Ri<X>:=PolynomialRing(Ki);
    //         Ei:=SplittingField(X^2-Twist[j]);
            


    //     end for;



    // end for; 



    return Triples;
end function;


function InertialTypes(F : SkipExceptionals := false) 
    c := 0;
    QuadExt,Twist:= AllQuadraticExtensions(F : Selmer:=true);
    print("Extensions done");

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    ff := Floor(N/2);
    printf "f=%o\n", ff;
    groups, maps, lift := UComplex(F, ff);
    #groups;

    PS := PrincipalSeries(F, ff : MyComplex := [*groups, maps, lift*]);
    #PS;
    [* [ c`Character`Order, c`CondExp ] : c in PS *];
    print("----");

    i := 1;
    // SCR:=[*0: t in [1..#QuadExt-1] *];
    // SCRChars :=[*0: t in [1..#QuadExt-1] *];   
    // SCRGroups:=[*0: t in [1..#QuadExt-1] *];
    // SCRLifts :=[*0: t in [1..#QuadExt-1] *];
    // SCRexp:=[];
    SCR := [* [] : _ in [1..#Twist] *];
    for t in [1..#QuadExt] do
        K:=QuadExt[t];
        i;
        Cond, pi, Gal, y := ExtValues(F,K);
        c := Cond;
        if Cond eq 0 then
            SCU := SupercuspidalUnramified(F,K,ff);
            [*[ c`Character`Order, c`CondExp ] : c in SCU*];
            printf "SCU: %o\n", #SCU;
            // [[*char[2],char[3]*] : char in chars];
        else 
            f := Max(N-Cond, 2*Cond);
            printf "f=%o\n", f;
            printf "c=%o\n", c;
            // G := groups[ff - c + 1];
            // if ff - c + 1 eq 1 then
            //     llift := lift;
            // else
            //     llift := Inverse(maps[ff - c]) * lift;
            // end if;

            G := groups[1];
            llift:=lift;

            VarepsGenerators := {K!llift(g) : g in Generators(G)};
            SCR_K := SupercuspidalRamified(F, K, f, c, VarepsGenerators);
            SCR[t] := SCR_K;
            //Rchars,Rgroup,Rlift,exp:=SupercuspidalRamified(F, K, f, c, VarepsGenerators);
            //SCRChars := Append(SCRChars,Rchars);
            //SCRGroups := Append(SCRGroups,Rgroup);
            //SCRLifts := Append(SCRLifts,Rlift);
            //SCRexp:=Append(SCRexp,exp);
            printf "%o characters\n", #SCR_K;
            // Sort([c`CondExp : c in SCRChars[t]]);
            // SCR_K;
            [*[ c`Character`Order, c`CondExp ] : c in SCR_K*];
            // [[*char[2],char[3]*] : char in chars];
            print("----");
        end if;
        i +:= 1;
    end for;

    Ex24:=[* *];
    Ex8:=[* *];
    if p eq 2 and not SkipExceptionals then
        // Ex24Groups:=[* *];
        // Ex8Groups:=[* *];
        // Ex24Lifts:=[* *];
        // Ex8Lifts:=[* *];
        // Ex24exp:=[];
        // Ex8exp:=[];
        if (in_deg mod 2 eq 0) then 
            for j in [1..3] do
                L:=FieldOfFractions(AllExtensions(F,3)[j]);
                Ex_L:=ExceptionalTypesTriply(F,L);
                Append(~Ex24, Ex_L);
            end for;
            L := FieldOfFractions(AllExtensions(F,3)[4]);
            Ex8 := ExceptionalTypesTriply(F,L);
        else 
            Ex24 := ExceptionalTypesSimply(F);
        end if;
    end if;

    return Twist, PS, SCU, SCR, Ex8, Ex24;
    // return Twist,PSChar,PSGroup,PSLift,PSExp,SCUChars,SCUGroup,SCULift,SCUexp,SCRChars,SCRGroups,SCRLifts,SCRexp,Ex8Chars,Ex8Groups,Ex8Lifts,Ex8exp,Ex24Chars,Ex24Groups,Ex24Lifts,Ex24exp;
end function;


ZZ:=Integers();
Q2:=pAdicField(2,200);
R<x>:=PolynomialRing(Q2);
Q4<phi>:=ext<Q2|x^2-x-1>;
R<x>:=PolynomialRing(Q4);
K1:=FieldOfFractions(AllExtensions(Q2,2)[1]);
K2:=UnramifiedExtension(Q2,3);
K3:=UnramifiedExtension(K2,2);
Degree(K3,Q2);


// F:=FieldOfFractions(AllExtensions(Q2,2)[6]);
time Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(Q4 : SkipExceptionals:=true);
// K := FieldOfFractions(AllExtensions(Q4, 2)[1]);

// load "CurvesQ4.m";
// load "EllipticCurves.m";

// Q3 := pAdicField(3,100);
// Q9 := UnramifiedExtension(Q3, 2);



// Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(Q4);
// // Twist,PSChar,PSGroup,PSLift,PSExp,SCUChars,SCUGroup,SCULift,SCUexp,SCRChars,SCRGroups,SCRLifts,SCRexp,Ex8Chars,Ex8Groups,Ex8Lifts,Ex8exp,Ex24Chars,Ex24Groups,Ex24Lifts,Ex24exp:=InertialTypes(Q2);

// InTypeOf(E[5,1],Twist, PS, SCU, SCR, Ex8, Ex24);