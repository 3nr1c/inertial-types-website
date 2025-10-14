load "inertial-types.m";

function Test_PS_Q2()
    F := pAdicField(2, 100);
    f := 4;

    Gens, Chars := PrincipalSeriesOfOrder(F,f,2);
    assert #Chars eq 3;
    assert #[c : c in Chars | c[2] eq 2] eq 1;
    assert #[c : c in Chars | c[2] eq 3] eq 2;

    Gens, Chars := PrincipalSeriesOfOrder(F,f,3);
    assert #Chars eq 0;

    Gens, Chars := PrincipalSeriesOfOrder(F,f,4);
    assert #Chars eq 2;
    assert #[c : c in Chars | c[2] eq 4] eq 2;

    Gens, Chars := PrincipalSeriesOfOrder(F,f,6);
    assert #Chars eq 0;

    return true;
end function;

function Test_PS_Q3()
    F := pAdicField(3, 100);
    f := 2;

    Gens, Chars := PrincipalSeriesOfOrder(F,f,2);
    assert #Chars eq 1;
    assert Chars[1][2] eq 1;

    Gens, Chars := PrincipalSeriesOfOrder(F,f,3);
    assert #Chars eq 1;
    assert Chars[1][2] eq 2;

    Gens, Chars := PrincipalSeriesOfOrder(F,f,4);
    assert #Chars eq 0;

    Gens, Chars := PrincipalSeriesOfOrder(F,f,6);
    assert #Chars eq 1;
    assert Chars[1][2] eq 2;

    return true;
end function;


function Test_PS_p_qeq_5()
    f := 2;

    Qp1 := pAdicField(13, 100);
    F1 := UnramifiedExtension(Qp1, 3);
    Gens, Chars4_1 := PrincipalSeriesOfOrder(F1,f,4);
    Gens, Chars3_1 := PrincipalSeriesOfOrder(F1,f,3);
    Gens, Chars6_1 := PrincipalSeriesOfOrder(F1,f,6);
    assert #Chars4_1 eq 1;
    assert Chars4_1[1][2] eq 1;
    assert #Chars3_1 eq 1;
    assert Chars3_1[1][2] eq 1;
    assert #Chars6_1 eq 1;
    assert Chars6_1[1][2] eq 1;

    Qp2 := pAdicField(5, 100);
    F2 := UnramifiedExtension(Qp2, 3);
    Gens, Chars4_2 := PrincipalSeriesOfOrder(F2,f,4);
    Gens, Chars3_2 := PrincipalSeriesOfOrder(F2,f,3);
    Gens, Chars6_2 := PrincipalSeriesOfOrder(F2,f,6);
    assert #Chars4_2 eq 1;
    assert Chars4_2[1][2] eq 1;
    assert #Chars3_2 eq 0;
    assert #Chars6_2 eq 0;

    Qp3 := pAdicField(7, 100);
    F3 := UnramifiedExtension(Qp3, 3);
    Gens, Chars4_3 := PrincipalSeriesOfOrder(F3,f,4);
    Gens, Chars3_3 := PrincipalSeriesOfOrder(F3,f,3);
    Gens, Chars6_3 := PrincipalSeriesOfOrder(F3,f,6);
    assert #Chars4_3 eq 0;
    assert #Chars3_3 eq 1;
    assert Chars3_3[1][2] eq 1;
    assert #Chars6_3 eq 1;
    assert Chars6_3[1][2] eq 1;

    Qp4 := pAdicField(11, 100);
    F4 := UnramifiedExtension(Qp4, 3);
    Gens, Chars4_4 := PrincipalSeriesOfOrder(F4,f,4);
    Gens, Chars3_4 := PrincipalSeriesOfOrder(F4,f,3);
    Gens, Chars6_4 := PrincipalSeriesOfOrder(F4,f,6);
    assert #Chars4_4 eq 0;
    assert #Chars3_4 eq 0;
    assert #Chars6_4 eq 0;

    return true;
end function;


Test_PS_Q2();
Test_PS_Q3();
Test_PS_p_qeq_5();