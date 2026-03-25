////////////////////////////////////////////////////////////////////////
// Pretty summary printer for induced character data
////////////////////////////////////////////////////////////////////////

function _Str(x)
    try
        return Sprint(x);
    catch e
        return "-";
    end try;
end function;

procedure _PrintTable(header, rows)
    if #rows eq 0 then
        print "(none)";
        return;
    end if;

    n := #header;

    widths := [ Max([#_Str(r[i]) : r in rows] cat [#_Str(header[i])])
                : i in [1..n] ];

    sep := "";
    for w in widths do
        sep cat:= "-"^(w+2);
    end for;

    print sep;

    for i in [1..n] do
        printf Sprintf("%%-%oo  ", widths[i]), header[i];
    end for;
    print "";

    print sep;

    for r in rows do
        for i in [1..n] do
            printf Sprintf("%%-%oo  ", widths[i]), _Str(r[i]);
        end for;
        print "";
    end for;

    print sep;
    
end procedure;

////////////////////////////////////////////////////////////////////////
// Row constructors
////////////////////////////////////////////////////////////////////////

function _InTypeRow(tau)
    return [*
        SemistabilityDefect(tau),
        tau`CondExp,
        tau`Character`Order
    *];
end function;


function _InTypeRowWithDesc(tau, desc)
    return [*
        SemistabilityDefect(tau),
        tau`CondExp,
        tau`Character`Order,
        desc
    *];
end function;

function _InTypeRowWithDescInertiaField(tau, desc)
    Qp := pAdicField(Prime(tau`BaseField), 100);
    poly := DefiningPolynomial(InertiaField(tau), Qp);
    R := Parent(poly);
    AssignNames(~R, ["X"]);
    return [*
        SemistabilityDefect(tau),
        tau`CondExp,
        tau`Character`Order,
        desc,
        poly
    *];
end function;


////////////////////////////////////////////////////////////////////////
// Row aggregation
////////////////////////////////////////////////////////////////////////

function _AggregateRows(rows)
    counts := AssociativeArray();

    for r in rows do
        key := <r[1], r[2], r[3], r[4]>;
        if IsDefined(counts, key) then
            counts[key] +:= 1;
        else
            counts[key] := 1;
        end if;
    end for;

    out := [];
    for k in Keys(counts) do
        Append(~out, [* k[1], k[2], k[3], k[4], counts[k] *]);
    end for;

    return Sort(out, func<x, y | (x[1] - y[1]) + 0.01*(x[2] - y[2])>);
end function;

////////////////////////////////////////////////////////////////////////
// Main summary procedure
////////////////////////////////////////////////////////////////////////

intrinsic PrintInertiaFields(PS, SCU, SCR, Ex8, Ex24)
{Prints a summary of the data outputed by InertialTypes(F)}
    printf "\n========================================\n";
    printf "    Computed Inertia Types : Summary\n";
    printf "========================================\n\n";

    printf "PrincipalSeries  : %o\n", #PS;
    printf "SCU              : %o\n", #SCU;
    printf "SCR              : %o\n", #SCR;
    printf "Ex8              : %o\n", #Ex8;
    printf "Ex24             : %o\n", #Ex24;
    printf "----------------------------------------\n";
    printf "Total inertial types : %o\n\n", #PS + #SCU + #SCR + #Ex8 + #Ex24;

    rows := [];

    ////////////////////////////////////////////////////////////////
    // Principal Series
    ////////////////////////////////////////////////////////////////

    if #PS gt 0 then
        rows cat:= [ _InTypeRowWithDescInertiaField(x, "principal series") : x in PS ];
    end if;

    ////////////////////////////////////////////////////////////////
    // SCU
    ////////////////////////////////////////////////////////////////

    if #SCU gt 0 then
        rows cat:= [ _InTypeRowWithDescInertiaField(x, "supercuspidal unramified") : x in SCU ];
    end if;

    ////////////////////////////////////////////////////////////////
    // SCR
    ////////////////////////////////////////////////////////////////

    if #SCR gt 0 then
        rows cat:= [ _InTypeRowWithDescInertiaField(x, "supercuspidal ramified") : x in SCR ];
    end if;


    ////////////////////////////////////////////////////////////////
    // Ex8
    ////////////////////////////////////////////////////////////////

    if #Ex8 gt 0 then
        rows cat:= [ _InTypeRowWithDescInertiaField(x, "exceptional, Q8") : x in Ex8 ];
    end if;

    ////////////////////////////////////////////////////////////////
    // Ex24
    ////////////////////////////////////////////////////////////////

    if #Ex24 gt 0 then
        rows cat:= [ _InTypeRowWithDescInertiaField(x, "exceptional, SL(2,3)") : x in Ex24 ];
    end if;

    _PrintTable(
        ["Semistability defect", "v(E)", "Character order", "Description", "Field of inertia"],
        rows
    );
end intrinsic;

intrinsic InTypesSummary(PS, SCU, SCR, Ex8, Ex24)
{Prints a summary of the data outputed by InertialTypes(F)}

    printf "\n========================================\n";
    printf "    Computed Inertia Types : Summary\n";
    printf "========================================\n\n";

    printf "PrincipalSeries  : %o\n", #PS;
    printf "SCU              : %o\n", #SCU;
    printf "SCR              : %o\n", #SCR;
    printf "Ex8              : %o\n", #Ex8;
    printf "Ex24             : %o\n", #Ex24;
    printf "----------------------------------------\n";
    printf "Total inertial types : %o\n\n", #PS + #SCU + #SCR + #Ex8 + #Ex24;

    rows := [];

    ////////////////////////////////////////////////////////////////
    // Principal Series
    ////////////////////////////////////////////////////////////////

    if #PS gt 0 then
        rows cat:= [ _InTypeRowWithDesc(x, "principal series") : x in PS ];
    end if;

    ////////////////////////////////////////////////////////////////
    // SCU
    ////////////////////////////////////////////////////////////////

    if #SCU gt 0 then
        rows cat:= [ _InTypeRowWithDesc(x, "supercuspidal unramified") : x in SCU ];
    end if;

    ////////////////////////////////////////////////////////////////
    // SCR
    ////////////////////////////////////////////////////////////////

    if #SCR gt 0 then
        rows cat:= [ _InTypeRowWithDesc(x, "supercuspidal ramified") : x in SCR ];
    end if;

    ////////////////////////////////////////////////////////////////
    // Ex8
    ////////////////////////////////////////////////////////////////

    if #Ex8 gt 0 then
        rows cat:= [ _InTypeRowWithDesc(x, "exceptional, Q8") : x in Ex8 ];
    end if;

    ////////////////////////////////////////////////////////////////
    // Ex24
    ////////////////////////////////////////////////////////////////

    if #Ex24 gt 0 then
        rows cat:= [ _InTypeRowWithDesc(x, "exceptional, SL(2,3)") : x in Ex24 ];
    end if;

    ////////////////////////////////////////////////////////////////
    // Aggregate identical rows
    ////////////////////////////////////////////////////////////////

    rows := _AggregateRows(rows);

    ////////////////////////////////////////////////////////////////
    // Print table
    ////////////////////////////////////////////////////////////////

    _PrintTable(
        ["e", "v(N)", "Character order", "Description", "Count"],
        rows
    );

end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
