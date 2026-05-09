
procedure PrintSummaryToFile(data, p, f, label, poly, url, filename)
    /* data: [* [* e, vN, charOrder, desc, count *], ... *]
       label, poly, url: Strings
    */
    
    file := Open(filename, "w");

    Fx := Parent(poly);
    AssignNames(~Fx, ["x"]);
    
    // Start JSON object
    fprintf file, "{\n";
    fprintf file, "  \"prime\": \"%o\",\n", p;
    fprintf file, "  \"f\": \"%o\",\n", f;
    fprintf file, "  \"label\": \"%o\",\n", label;
    fprintf file, "  \"polynomial\": \"%o\",\n", poly;
    fprintf file, "  \"lmfdb_url\": \"%o\",\n", url;
    fprintf file, "  \"table\": [\n";
    
    for i in [1..#data] do
        entry := data[i];
        fprintf file, "    {\n";
        fprintf file, "      \"e\": %o,\n", entry[1];
        fprintf file, "      \"v(N)\": %o,\n", entry[2];
        fprintf file, "      \"character order\": %o,\n", entry[3];
        fprintf file, "      \"description\": \"%o\",\n", entry[4];
        fprintf file, "      \"count\": %o\n", entry[5];
        
        // Don't print a comma after the last array element
        if i lt #data then
            fprintf file, "    },\n";
        else
            fprintf file, "    }\n";
        end if;
    end for;
    
    // Close array and object
    fprintf file, "  ]\n";
    fprintf file, "}\n";
    
    delete file;
    print "JSON exported to", filename;
end procedure;

function ExportTauToJSON(tau, name, base_field, inertia_poly)
    // Convert the p-adic polynomial to a string with integer coefficients
    name;
    Fx := Parent(inertia_poly);
    AssignNames(~Fx, ["x"]);
    F := BaseRing(tau);
    AssignNames(~F, ["a"]);
    if AbsoluteDegree(BaseRing(inertia_poly)) eq 1 then
        Z := Integers();
        Zx<x> := PolynomialRing(Z);
        int_coeffs := [ Z ! c : c in Coefficients(inertia_poly) ];
        poly_int := Zx ! int_coeffs;
        poly_string := Sprintf("%o", poly_int);
    else
        poly_string := Sprintf("%o", inertia_poly);
    end if;

    // Strip out any line breaks and continuation backslashes Magma might have added
    poly_string := SubstituteString(poly_string, "\n", "");
    poly_string := SubstituteString(poly_string, "\\", "");

    // Extract available data from tau
    e := SemistabilityDefect(tau);
    v_N := tau`CondExp;
    char_order := tau`Character`Order;
    char_condexp := tau`Character`CondExp;
    tau_type := Type(tau);
    
    // Determine the description based on Type(tau)
    description := "unknown";
    if tau_type eq PSInType then
        description := "principal series";
    elif tau_type eq SCUInType then
        description := "supercuspidal unramified";
    elif tau_type eq SCRInType then
        description := "supercuspidal ramified";
    elif tau_type eq TriplyImprInType then
        description := "supercuspidal ramified";
    elif tau_type eq ExceptionalInType then
        if e eq 8 then
            description := "exceptional, Q8";
        elif e eq 24 then
            description := "exceptional, SL(2,3)";
        end if;
    end if;
    
    SetColumns(0);
    // Construct the JSON string
    json_format := 
        "{\n" cat
        "  \"Name\": \"%o\",\n" cat
        "  \"Base Field\": \"%o\",\n" cat
        "  \"Description\": \"%o\",\n" cat
        "  \"e\": %o,\n" cat
        "  \"v(N)\": %o,\n" cat
        "  \"Character Order\": %o,\n" cat
        "  \"Character CondExp\": %o,\n" cat
        "  \"inertia_field\": {\n" cat
        "    \"polynomial\": \"%o\"\n" cat
        "  },\n";

    if Type(tau) eq ExceptionalInType then
        L := BaseRing(BaseRing(tau`Character));
        Fmu := BaseField(L);
        if Degree(Fmu, F) eq 2 then
            AssignNames(~Fmu, ["\\\\mu_3"]);
        end if;
        AssignNames(~L, ["b"]);
        triply_poly := DefiningPolynomial(L, Fmu);
        Fmux := Parent(triply_poly);
        AssignNames(~Fmux, ["x"]);

        json_format := json_format cat
        "  \"triply_field\": {\n";
        json_format := json_format cat
        Sprintf("    \"polynomial\": \"%o\"\n  },\n", triply_poly);
    end if;
    
    json_format := json_format cat
        "  \"inducing_field\": {\n" cat
        "    \"polynomial\": \"%o\"\n" cat
        "  },\n";
    inducing_poly := DefiningPolynomial(tau`Character`Field, BaseField(tau`Character`Field));
    Lx := Parent(inducing_poly);
    AssignNames(~Lx, ["x"]);

    K := BaseField(tau`Character);
    if Type(tau) eq PSInType then
        AssignNames(~K, ["a"]);
    elif Type(tau) ne ExceptionalInType then
        AssignNames(~K, ["b"]);
    else
        AssignNames(~K, ["c"]);
    end if;
    Zm := Codomain(tau`Character`Map);
    Gens := [tau`Character`Lift(g) : g in Generators(Domain(tau`Character`Map))];
    Vals := [[i : i in [0..tau`Character`Order-1] | tau`Character(g) eq Zm!i][1] : g in Gens];
    json_format := json_format cat 
        "  \"char_values\": [\n";
    for i in [1..#Gens] do
        json_format := json_format cat
            Sprintf("    {\n      \"gen\": \"%o\",\n", Gens[i]) cat
            Sprintf("      \"val\": \"%o\"\n    }", Vals[i]);
        if i lt #Gens then json_format := json_format cat ","; end if;
        json_format := json_format cat "\n";
    end for;
    json_format := json_format cat "  ]\n"; 

    json_format := json_format cat "}";

    json_string := Sprintf(json_format, name, base_field, description, e, v_N, char_order, 
        char_condexp, poly_string, inducing_poly);


    return json_string;
end function;

procedure ExportTauListToJSON(TypeList, base_field)
    counts := AssociativeArray();
    alphabet := ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"];

    // first we sort the taus according to their character values
    Values := [];
    for tau in TypeList do
        Gens := [tau`Character`Lift(g) : g in Generators(Domain(tau`Character`Map))];

        Zm := Codomain(tau`Character`Map);
        Append(~Values, [[i : i in [0..tau`Character`Order-1] | tau`Character(g) eq Zm!i][1] : g in Gens]);
    end for;
    Sort(~Values, ~permut);
    TypeList := [TypeList[i^permut] : i in [1..#TypeList]];

    QuadDisc := [];

    for tau in TypeList do
        F := BaseField(tau);
        if #QuadDisc eq 0 then
            QuadDisc := [Discriminant(FieldOfFractions(K),F) : K in AllExtensions(F, 2)];
        end if;
        // Extract necessary parameters to build the label
        e := SemistabilityDefect(tau);
        v_N := tau`CondExp;
        char_order := tau`Character`Order;
        tau_type := Type(tau);
        l := 1;
        k := 1;
        
        // Determine type abbreviation for the label
        type_abbr := "unknown";
        if tau_type eq PSInType then
            type_abbr := "ps";
        elif tau_type eq SCUInType then
            type_abbr := "scu";
            k := 2^(AbsoluteDegree(F) + 2) - 1;
        elif tau_type eq SCRInType then
            type_abbr := "scr";
            k := Index([IsSquare(tau`Character`Field!d) : d in QuadDisc], true);
        elif tau_type eq TriplyImprInType then
            type_abbr := "scr";
            ks := Sort([
                Index([IsSquare(tau`InducingFields[1]!d) : d in QuadDisc], true),
                Index([IsSquare(tau`InducingFields[2]!d) : d in QuadDisc], true),
                Index([IsSquare(tau`InducingFields[3]!d) : d in QuadDisc], true)
            ]);
            k := Sprintf("%o_%o_%o", ks[1], ks[2], ks[3]);
        elif tau_type eq ExceptionalInType then
            type_abbr := "ex";
            if AbsoluteInertiaDegree(F) mod 2 eq 0 then
                l := Index([IsIsomorphic(FieldOfFractions(L), tau`TriplyField) : L in AllExtensions(F, 3)], true);
            end if;
            QuadOfL := [Discriminant(FieldOfFractions(K), tau`TriplyField) : K in AllExtensions(tau`TriplyField, 2)];
            ks := Sort([
                Index([IsSquare(tau`Triply`InducingFields[1]!d) : d in QuadOfL], true),
                Index([IsSquare(tau`Triply`InducingFields[2]!d) : d in QuadOfL], true),
                Index([IsSquare(tau`Triply`InducingFields[3]!d) : d in QuadOfL], true)
            ]);
            k := Sprintf("%o_%o_%o", ks[1], ks[2], ks[3]);
        end if;

        // type.e.v(N).i.j.X
        // i -> 1, si no excepcional, else indice de la cubica del triply field
        // j -> 1, si ps, else indice de la cuadratica del inducing field en AllExtensions(L, 2);
        
        // Generate the prefix string: type.v(N).CharacterOrder
        prefix := Sprintf("%o.%o.%o.%o.%o", type_abbr, e, v_N, l, k);
        
        // Handle collisions to get the 'x' letter
        b, count := IsDefined(counts, prefix);
        if b then
            counts[prefix] := count + 1;
        else
            counts[prefix] := 1;
        end if;
        
        idx := counts[prefix];
        if idx le 26 then
            letter := alphabet[idx];
        else
            // Fallback for > 26 collisions
            letter := "z" cat IntegerToString(idx); 
        end if;
        
        // Final name string for the JSON property
        name := prefix cat "." cat letter;
        
        // Generate the inertia polynomial
        inertia_poly := "";
        N := InField(tau);
        F := BaseField(tau);
        inertia_poly := DefiningPolynomial(Integers(N), Integers(F));
        if true or Degree(inertia_poly) le 12 then
            try
                inertia_poly := PolRedPadic(inertia_poly, Integers(F));
                "Used PolRedPadic";
            catch e
                if Type(tau) eq ExceptionalInType then
                    inertia_poly := BetterPoly(inertia_poly, N, F, tau);
                else 
                    inertia_poly := BetterPoly(inertia_poly, N, F);
                end if;
                "Used BetterPoly";
            end try;
        end if;
        
        // Call the recycled function to generate the JSON string
        json_string := ExportTauToJSON(tau, name, base_field, inertia_poly);
        
        // Construct the filename: base_field.name.json
        filename := Sprintf("../_data/types/%o/%o-%o.json", base_field, base_field, name);
        
        // Disable wrapping
        SetColumns(0);

        // Write out the JSON string, overwriting the file if it already exists
        PrintFile(filename, json_string : Overwrite := true);
    end for;
end procedure;