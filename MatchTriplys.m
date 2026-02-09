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

    TriplyImprimitives := [];

    for l in [1..1] do
        counter:=0;
        for triply in Triples do
            
            i,j,k:=Explode(SetToSequence(triply));
            y1:=Twist[i];
            y2:=Twist[j];
            y3:=Twist[k];
            Ki:=SCR[i,1]`Character`Field;
            Kj:=SCR[j,1]`Character`Field;
            Kk:=SCR[k,1]`Character`Field;
            Ri<X>:=PolynomialRing(Ki);
            Ei:=SplittingField(X^2-Twist[j]);
            s1:=Sqrt(Ki!y1);
            s2:=Sqrt(Ei!y2);
            s3:=Sqrt(Ei!y3);
            c:=Max([tau`Character`CondExp: tau in SCR[i]]);
            Uf,UpStairsUf:=OptimalNorms(Ei,Ki,c);
            UnitCoordsKi:=[ElementCoordinates(g,[1,s2]): g in UpStairsUf];
            UnitCoordsF:=[ElementCoordinates(x[1], [1,s1]) cat ElementCoordinates(x[2], [1,s1]) : x in UnitCoordsKi];
            ManualUfi:=[ u[1]^2+u[2]^2*y1-u[3]^2*y2-u[4]^2*y1*y2+(2*u[1]*u[2]-2*u[3]*u[4]*y2)*s1 :u in UnitCoordsF];
            s2:=Sqrt(Kj!y2);
            ManualUfj:=[ u[1]^2+u[3]^2*y2-u[2]^2*y1-u[4]^2*y1*y2+(2*u[1]*u[3]-2*u[2]*u[4]*y1)*s2 :u in UnitCoordsF];
            
            UnitCoordsKi:=[ElementCoordinates(g,[1,s3]): g in UpStairsUf];
            UnitCoordsF:=[ElementCoordinates(x[1], [1,s1]) cat ElementCoordinates(x[2], [1,s1]) : x in UnitCoordsKi];
            s3:=Sqrt(Kk!y3);
            ManualUfk:=[ u[1]^2+u[3]^2*y3-u[2]^2*y1-u[4]^2*y1*y3+(2*u[1]*u[3]-2*u[2]*u[4]*y1)*s3 :u in UnitCoordsF];
            
            
            for chi in SCR[i] do
                Matchj:=SCR[j];
                Matchk:=SCR[k];
                isIsoj, isoj := IsIsomorphic(Codomain(chi`Character`Map), Codomain(SCR[j,1]`Character`Map));
                isIsok, isok := IsIsomorphic(Codomain(chi`Character`Map), Codomain(SCR[k,1]`Character`Map));
                
                for t in [1..#ManualUfi] do
                    Matchj:=[tau: tau in Matchj   | isoj(chi`Character(Inverse(chi`Character`Lift)(ManualUfi[t]))) eq tau`Character(Inverse(tau`Character`Lift)(ManualUfj[t]))];
                    Matchk:=[tau: tau in Matchk   | isok(chi`Character(Inverse(chi`Character`Lift)(ManualUfi[t]))) eq tau`Character(Inverse(tau`Character`Lift)(ManualUfk[t]))];
                end for;      
            Matchj;
            Matchk;
            if #Matchj eq 1 and #Matchk eq 1 then
                Append(~TriplyImprimitives, NewTriplyImprimitiveIT([
                    chi`Character, Matchj[1]`Character, Matchk[1]`Character
                ], chi`BaseField));
            elif not (#Matchj eq 0 and #Matchk eq 0) then
                print("ERROR");
                assert false;
            end if;

            print("-------------------------------------------");
            end for;
            

        end for;



    end for; 
    return TriplyImprimitives;
end function;

TriplyImprimitives:=MatchTriplys (Q4,SCR,Twist);