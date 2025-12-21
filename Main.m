load "Exceptionals.m";


function InertialTypes(F) 
    c := 0;
    QuadExt,Twist:= AllQuadraticExtensions(F);

    p, ram_deg, in_deg, pi, N := BaseValues(F);
    ff := Floor(N/2);
    printf "f=%o\n", ff;
    groups, maps, lift := UComplex(F, ff);
    #groups;

    PSChar := PrincipalSeries(F, ff : MyComplex := [*groups, maps, lift*]);
    PSGroup:=groups[1];
    PSLift:=lift;
    PSExp:=#groups;
    #PSChar;
    [*[ c`Character`Order, c`CondExp ] : c in PSChar*];
    // [[*char[2],char[3]*] : char in chars];
    print("----");

    i := 1;
    SCR:=[*0: t in [1..#QuadExt-1] *];
    SCRChars :=[*0: t in [1..#QuadExt-1] *];   
    SCRGroups:=[*0: t in [1..#QuadExt-1] *];
    SCRLifts :=[*0: t in [1..#QuadExt-1] *];
    SCRexp:=[];
    for t in [1..#QuadExt] do
        K:=QuadExt[t];
        i;
        Cond, pi, Gal, y := ExtValues(F,K);
        c := Cond;
        if Cond eq 0 then
            SCUChars,SCUGroup,SCULift,SCUexp := SupercuspidalUnramified(F,K,ff);
            [*[ c`Character`Order, c`CondExp ] : c in SCUChars*];
            printf "SCU: %o\n", #SCUChars;
            // [[*char[2],char[3]*] : char in chars];
        else 
            f := Max(N-Cond, 2*Cond);
            printf "f=%o\n", f;
            printf "c=%o\n", c;
            G := groups[ff - c + 1];
            if ff - c + 1 eq 1 then
                llift := lift;
            else
                llift := Inverse(maps[ff - c]) * lift;
            end if;
            VarepsGenerators := {K!llift(g) : g in Generators(G)};
            SCRChars[t],SCRGroups[t],SCRLifts[t],SCRexp[t]:=SupercuspidalRamified(F, K, f, c, VarepsGenerators);
            //Rchars,Rgroup,Rlift,exp:=SupercuspidalRamified(F, K, f, c, VarepsGenerators);
            //SCRChars := Append(SCRChars,Rchars);
            //SCRGroups := Append(SCRGroups,Rgroup);
            //SCRLifts := Append(SCRLifts,Rlift);
            //SCRexp:=Append(SCRexp,exp);
            printf "%o characters\n", #SCRChars[t];
            // Sort([c`CondExp : c in SCRChars[t]]);
            [*[ c`Character`Order, c`CondExp ] : c in SCRChars[t]*];
            // [[*char[2],char[3]*] : char in chars];
            print("----");
        end if;
        i +:= 1;
    end for;

    if p eq 2 then
        Ex24Chars:=[* *];
        Ex8Chars:=[* *];
        Ex24Groups:=[* *];
        Ex8Groups:=[* *];
        Ex24Lifts:=[* *];
        Ex8Lifts:=[* *];
        Ex24exp:=[];
        Ex8exp:=[];
        if (in_deg mod 2 eq 0) then 
            for j in [1..3] do
                L:=FieldOfFractions(AllExtensions(F,3)[j]);
                Char,ExG,ExL,exp:=ExceptionalTypesTriply(F,L);
                Ex24Chars:=Append(Ex24Chars,Char);
                Ex24Groups:=Append(Ex24Groups,ExG);
                Ex24Lifts:=Append(Ex24Lifts,ExL);
                Ex24exp:=Append(Ex24exp,exp);
            end for;
            L:=FieldOfFractions(AllExtensions(F,3)[4]);
            Ex8Chars,Ex8Groups,Ex8Lifts,Ex8exp:=ExceptionalTypesTriply(F,L);
        else 
            Ex24Chars,Ex24Groups,Ex24Lifts,Ex24exp:=ExceptionalTypesSimply(F);
        end if;
    end if;

    return Twist,PSChar,PSGroup,PSLift,PSExp,SCUChars,SCUGroup,SCULift,SCUexp,SCRChars,SCRGroups,SCRLifts,SCRexp,Ex8Chars,Ex8Groups,Ex8Lifts,Ex8exp,Ex24Chars,Ex24Groups,Ex24Lifts,Ex24exp;
end function;


ZZ:=Integers();
Q2:=pAdicField(2,100);
R<x>:=PolynomialRing(Q2);
Q4<phi>:=ext<Q2|x^2-x-1>;
K := FieldOfFractions(AllExtensions(Q4, 2)[1]);

load "CurvesQ4.m";
load "EllipticCurves.m";

Q3 := pAdicField(3,100);
Q9 := UnramifiedExtension(Q3, 2);



Twist,PSChar,PSGroup,PSLift,PSExp,SCUChars,SCUGroup,SCULift,SCUexp,SCRChars,SCRGroups,SCRLifts,SCRexp,Ex8Chars,Ex8Groups,Ex8Lifts,Ex8exp,Ex24Chars,Ex24Groups,Ex24Lifts,Ex24exp:=InertialTypes(Q2);

InTypeOf(ExE[7,22],Twist,PSChar,PSGroup,PSLift,PSExp,SCUChars,SCUGroup,SCULift,SCUexp,SCRChars,SCRGroups,SCRLifts,SCRexp,Ex8Chars,Ex8Groups,Ex8Lifts,Ex8exp,Ex24Chars,Ex24Groups,Ex24Lifts,Ex24exp);