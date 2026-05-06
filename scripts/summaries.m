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


function SummaryTable(PS, SCU, SCR, Ex8, Ex24)
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

    return _AggregateRows(rows);
end function;