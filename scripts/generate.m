AttachSpec("../../inertial-types/spec");
AttachSpec("../../padic_db/spec");
load "summaries.m";
load "printing.m";

SetVerbose("InTypes", 2);
SetVerbose("InFields", 1);

p := 2;
Qp := pAdicField(p,100);
// F := Qp; 
// F := UnramifiedExtension(Qp, 3);
F := FieldOfFractions(AllExtensions(Qp, 3)[1]);

d := Degree(F, Qp);
e := RamificationDegree(F, Qp);
f := Integers()!(d div e);
c := Valuation(Discriminant(F, Qp));
label := Sprintf("%o.%o.%o.%oa1.1", p, f, e, c);//Change the label accordingly!!
poly := DefiningPolynomial(F,Qp);

label;
poly;

url := Sprintf("https://www.lmfdb.org/padicField/%o", label);

// This will create the folder if it doesn't exist and do nothing if it does.
System(Sprintf("mkdir -p ../_data/types/%o", label));

F;
PS, SCU, SCR, Ex8, Ex24, Twist := InTypes(F : SkipExceptionals := true, InFields := false);
// InTypesSummary(PS, SCU, SCR, Ex8, Ex24);

// table := SummaryTable(PS, SCU, SCR, Ex8, Ex24);
// PrintSummaryToFile(table, p, f, label, poly, url, Sprintf("../_data/fields/%o.json", label));

// ExportTauListToJSON(PS, label);
// ExportTauListToJSON(SCU, label);
// ExportTauListToJSON(SCR, label);


if p eq 2 then
    Ex8, Ex24 := ExceptionalTypes(F : InFields := true);
    table := SummaryTable(PS, SCU, SCR, Ex8, Ex24);
    PrintSummaryToFile(table, p, f, label, poly, url, Sprintf("../_data/fields/%o.json", label));

    ExportTauListToJSON(Ex8, label);
    ExportTauListToJSON(Ex24, label);
end if;
