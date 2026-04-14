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

function _InTypeRowWithDesc(tau, desc)
    return [*
        SemistabilityDefect(tau),
        tau`CondExp,
        tau`Character`Order,
        desc
    *];
end function;

////////////////////////////////////////////////////////////////////////
// Row aggregation
////////////////////////////////////////////////////////////////////////

function _AggregateRows(rows)
    counts := AssociativeArray();

    for r in rows do
        key := <ri : ri in r>;
        if IsDefined(counts, key) then
            counts[key] +:= 1;
        else
            counts[key] := 1;
        end if;
    end for;

    out := [];
    for k in Keys(counts) do
        Append(~out, [* ki : ki in k *] cat [* counts[k] *]);
    end for;

    return Sort(out, func<x, y | (x[1] - y[1]) + 0.01*(x[2] - y[2])>);
end function;

////////////////////////////////////////////////////////////////////////
// Main summary procedure
////////////////////////////////////////////////////////////////////////

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

    if #PS gt 0 then
        rows cat:= [ _InTypeRowWithDesc(x, "principal series") : x in PS ];
    end if;

    if #SCU gt 0 then
        rows cat:= [ _InTypeRowWithDesc(x, "supercuspidal unramified") : x in SCU ];
    end if;

    if #SCR gt 0 then
        rows cat:= [ _InTypeRowWithDesc(x, "supercuspidal ramified") : x in SCR ];
    end if;

    if #Ex8 gt 0 then
        rows cat:= [ _InTypeRowWithDesc(x, "exceptional, Q8") : x in Ex8 ];
    end if;

    if #Ex24 gt 0 then
        rows cat:= [ _InTypeRowWithDesc(x, "exceptional, SL(2,3)") : x in Ex24 ];
    end if;

    rows := _AggregateRows(rows);

    _PrintTable(
        ["e", "v(N)", "Character order", "Description", "Count"],
        rows
    );

end intrinsic;

intrinsic InTypesSummary(PS, SCU, SCR)
{}
    InTypesSummary(PS, SCU, SCR, [], []);
end intrinsic;

intrinsic SCRSummary(SCR, Twist)
{}
    printf "\n========================================\n";
    printf "    Supercuspidal Ramified Summary \n";
    printf "========================================\n\n";
    rows := [];

    F := SCR[1]`BaseField;
    triplys := AbsoluteInertiaDegree(F) mod 2 eq 0;

    for tau in SCR do
        row := _InTypeRow(tau);
        if triplys then
            i1 := Index([IsSquare(tau`InducingFields[1]!t) : t in Twist], true);
            i2 := Index([IsSquare(tau`InducingFields[2]!t) : t in Twist], true);
            i3 := Index([IsSquare(tau`InducingFields[3]!t) : t in Twist], true);
            row := [* row[1], row[2] *] cat [* Sprintf("[K%o, K%o, K%o]", i1, i2, i3) *];
        else 
            i := Index([IsSquare(tau`InducingField!t) : t in Twist], true);
            row := [* row[1], row[2] *] cat [* Sprintf("K%o", i) *];
        end if;
        Append(~rows, row);
    end for;

    rows := _AggregateRows(rows);

    if triplys then
        _PrintTable(
            ["e", "v(N)", "Inducing fields", "Count" ],
            rows
        );
    else
        _PrintTable(
            ["e", "v(N)", "Inducing field", "Count"],
            rows
        );
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
