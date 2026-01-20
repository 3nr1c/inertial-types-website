177,0
T,InertiaCharacter,-,0
A,InertiaCharacter,6,GrpExp,CondExp,Field,Lift,Order,Map
S,NewInertiaCharacter,Create an inertia character,2,4,1,82,0,108,5,1,82,0,108,6,0,0,0,0,0,0,0,82,,0,0,82,,0,0,-1,,0,0,148,,0,0,148,,0,0,148,,InertiaCharacter,-38,-38,-38,-38,-38
S,@,Return the image of x through the character phi,0,2,0,0,0,0,0,0,0,InertiaCharacter,,0,0,-1,,-1,-38,-38,-38,-38,-38
S,Print,Print phi,0,1,0,0,1,0,0,0,0,InertiaCharacter,,-38,-38,-38,-38,-38,-38
S,*,"Return phi * psi, as long as they have coprime orders",0,2,0,0,0,0,0,0,0,InertiaCharacter,,0,0,InertiaCharacter,,InertiaCharacter,-38,-38,-38,-38,-38
S,*,Do all products of a character from each list,2,0,1,82,0,InertiaCharacter,1,1,82,0,InertiaCharacter,2,0,0,0,0,0,0,0,82,,0,0,82,,82,-38,-38,-38,-38,-38
T,InertiaType,-,0
A,InertiaType,3,BaseField,CondExp,Character
S,eq,Determines whether the two types are isomorphic as representations of inertia,0,2,0,0,0,0,0,0,0,InertiaType,,0,0,InertiaType,,36,-38,-38,-38,-38,-38
S,in,Returns whether tau is in list,1,1,1,82,0,InertiaType,2,0,0,0,0,0,0,0,82,,0,0,InertiaType,,36,-38,-38,-38,-38,-38
T,NullIT,-,1,InertiaType
S,IsNull,Returns true if and only if tau is of type NullIT,0,1,0,0,0,0,0,0,0,InertiaType,,36,-38,-38,-38,-38,-38
S,Print,Print tau,0,1,0,0,1,0,0,0,0,InertiaType,,-38,-38,-38,-38,-38,-38
S,Print,Print the Null Inertia Type,0,1,0,0,1,0,0,0,0,NullIT,,-38,-38,-38,-38,-38,-38
T,PrincipalSeriesIT,-,1,InertiaType
S,NewPrincipalSeriesIT,Create the principal series inertia type given by the character phi,0,1,0,0,0,0,0,0,0,InertiaCharacter,,PrincipalSeriesIT,-38,-38,-38,-38,-38
S,Print,Print tau,0,1,0,0,1,0,0,0,0,InertiaType,,-38,-38,-38,-38,-38,-38
T,SupercuspidalUnramifiedIT,-,1,InertiaType
S,NewSupercuspidalUnramifiedIT,Create the supercuspidal unramified inertia type of F induced by the character phi,0,2,0,0,0,0,0,0,0,400,,0,0,InertiaCharacter,,SupercuspidalUnramifiedIT,-38,-38,-38,-38,-38
T,SupercuspidalRamifiedIT,-,1,InertiaType
A,SupercuspidalRamifiedIT,1,InducingField
S,NewSupercuspidalRamifiedIT,Create the supercuspidal ramified inertia type of F induced by the character phi,0,2,0,0,0,0,0,0,0,400,,0,0,InertiaCharacter,,SupercuspidalRamifiedIT,-38,-38,-38,-38,-38
T,ExceptionalIT,-,1,InertiaType
A,ExceptionalIT,1,CubicField
S,NewExceptionalIT,Create the exceptional inertia type of F given by the character phi,0,3,0,0,0,0,0,0,0,400,,0,0,400,,0,0,InertiaCharacter,,ExceptionalIT,-38,-38,-38,-38,-38
S,SemistabilityDefect,Returns the semistability defect of tau,0,1,0,0,0,0,0,0,0,InertiaType,,148,-38,-38,-38,-38,-38
