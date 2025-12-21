178,0
T,InertiaCharacter,-,0
A,InertiaCharacter,5,CondExp,Field,Lift,Order,Map
S,NewInertiaCharacter,Create an inertia character,2,3,1,82,0,108,4,1,82,0,108,5,0,0,0,0,0,0,0,82,,0,0,82,,0,0,-1,,0,0,148,,0,0,148,,InertiaCharacter,-38,-38,-38,-38,-38
S,Print,Print phi,0,1,0,0,1,0,0,0,0,InertiaCharacter,,-38,-38,-38,-38,-38,-38
S,*,"Return phi * psi, as long as they have coprime orders",0,2,0,0,0,0,0,0,0,InertiaCharacter,,0,0,InertiaCharacter,,InertiaCharacter,-38,-38,-38,-38,-38
S,*,Do all products of a character from each list,2,0,1,82,0,InertiaCharacter,1,1,82,0,InertiaCharacter,2,0,0,0,0,0,0,0,82,,0,0,82,,82,-38,-38,-38,-38,-38
T,InertiaType,-,0
A,InertiaType,3,BaseField,CondExp,Character
S,Print,Print tau,0,1,0,0,1,0,0,0,0,InertiaType,,-38,-38,-38,-38,-38,-38
T,PrincipalSeriesIT,-,1,InertiaType
A,PrincipalSeriesIT,1,Character
S,NewPrincipalSeriesIT,Create the principal series inertia type given by the character phi,0,1,0,0,0,0,0,0,0,InertiaCharacter,,PrincipalSeriesIT,-38,-38,-38,-38,-38
T,SupercuspidalUnramifiedIT,-,1,InertiaType
A,SupercuspidalUnramifiedIT,1,Character
S,NewSupercuspidalUnramifiedIT,Create the supercuspidal unramified inertia type of F induced by the character phi,0,2,0,0,0,0,0,0,0,400,,0,0,InertiaCharacter,,SupercuspidalUnramifiedIT,-38,-38,-38,-38,-38
T,SupercuspidalRamifiedIT,-,1,InertiaType
A,SupercuspidalRamifiedIT,2,InducingField,Character
S,NewSupercuspidalRamifiedIT,Create the (simply imprimitive) supercuspidal ramified inertia type of F induced by the character phi,0,2,0,0,0,0,0,0,0,400,,0,0,InertiaCharacter,,SupercuspidalRamifiedIT,-38,-38,-38,-38,-38
T,TriplyImprimitiveIT,-,1,InertiaType
A,TriplyImprimitiveIT,2,InducingFields,Characters
