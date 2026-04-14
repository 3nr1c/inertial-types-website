# inertial-types

Magma package to compute inertial types attached to elliptic curves over finite extensions of Qp.


## Quick start

To use the package you may simply attach our spec:

```magma
AttachSpec("path/to/this/repo/spec");
```

A few basic examples have been provided. For instance, we may compute all inertial types over the field Q4:

```magma
AttachSpec("../spec");

SetVerbose("InTypes", true);

Q2 := pAdicField(2, 100);
Q4 := UnramifiedExtension(Q2, 2);

PS, SCU, SCR, Ex8, Ex24, Twist := InTypes(Q4);
``` 

The outputs of ```InTypes``` are documented in the sections below. Inertial types have some attributes that can be accessed:

```magma
// continue from above
tau := PS[8];
print(tau);
// Output:
// Inertia Type of the field
//         Unramified extension defined by the polynomial x^2 + x + 1 + O(2^100) 
// over 2-adic field mod 2^100
// of conductor exponent 2
// with underlying character of order 3 and conductor exponent 1

print(tau`CondExp);// prints 2
print(tau`BaseField);// prints the field Q4

phi := tau`Character; // this is the character inducing the type tau
// we can evaluate the character at units, for instance
phi(Q4.1); // outputs 2
``` 
To compute an inertia field, run ```InField(tau)```. Running ```InTypes(Q4 : InFields:=true)``` computes all inertia fields, which takes less time on average.

## Functions

- ```PrincipalSeries(F : Order := 0, TrivialOn := [], QuadraticOn := []) -> SeqEnum[PSInType]```
  
    Computes the inertial types of the principal series representations of F.
- ```SupercuspidalUnramified(F : Order := 0, TrivialOn := [], QuadraticOn := []) -> SeqEnum[SCUInType]```
  
    Computes the inertial types of the supercuspidal unramified representations of F.
- ```SupercuspidalRamified(F::FldPad : QuadExt := [], Twist := []) -> SeqEnum[SCRInType]```
  
    Computes the inertial types of the supercuspidal ramified representations of F that are not exceptional.
- ```SupercuspidalRamified(F::FldPad, K::FldPad) -> SeqEnum[SCRInType]```
  
    Computes the inertial types of the supercuspidal ramified representations of F that are induced from characters of the field K. The extension K/F must be ramified.
- ```SupercuspidalRamified(F, K::SeqEnum[FldPad]) -> SeqEnum[SCRInType]```
  
    Computes the inertial types of the supercuspidal ramified representations of F that are induced from all fields in the sequence K. This sequence of fields must satisfy:
    - #K <= 3
    - #K may be > 1 only if F contains the cubic roots of unity.
    - If #K == 3, the compositum of two fields in K must contain the third one.
- ```ExceptionalTypes(F::FldPad : InFields := false) -> SeqEnum[ExceptionalInType], SeqEnum[ExceptionalInType]```
  
    Computes the inertial types of the supercuspidal ramified representations of F that are exceptional. The output returns two sequences:
    - The first contains representations with image of inertia equal to the quaternion group.
    - The second contains representations with image of inertia equal to SL(2,3).
      
    Running with ```InFields:=true``` computes the inertia fields of all types, and is the recommended option if many of these fields are needed. This cuts the computation time by a large factor (equal to half the number of quadratic extensions of F) by taking advantage of twists.
- ```ExceptionalTypes(F::FldPad, L::FldPad : InFields := false) -> SeqEnum[ExceptionalInType]```
  
    Same as above, but returns only representations that become triply imprimitive over the field L.
    The extension L/F is always Galois, and satisfies:
    - If F contains the cubic roots of unity, then L/F is cubic.
    - If F does not contain the cubic roots of unity, then L is a cubic extension of the quadratic extension F(sqrt(-1)).
- ```ExceptionalTypes(F::FldPad, L::FldPad, K::FldPad : InFields := false) -> SeqEnum[ExceptionalInType]```
  
    Same as above, but returns only representations that become triply imprimitive over the field L, which in turn are induced from the quadratic extension K of L.
- ```InTypes(F :: FldPad : SkipExceptionals := false, InFields := false)```
  
    Runs all functions in order, returning:
    - A list of Principal Series Types
    - A list of Supercuspidal Unramified Types
    - A list of Supercuspidal Ramified Types
    - A list of Exceptional Types of size 8
    - A list of Exceptional Types of size 24
    - A list of values in F giving all used quadratic twists
      
    Running with ```SkipExceptionals:=true``` only computes principal series, supercuspidal unramified and supercuspidal ramified. Running with ```InFields:=true``` takes longer, but is the recommended option especially if one needs many inertia fields of exceptional types.


## Printing summaries

The intrinsics ```InTypesSummary(PS, SCU, SCR)``` and ```InTypesSummary(PS, SCU, SCR, Ex8, Ex24)``` are available to produce tables with counts of inertial types. A sample output is the following, which reproduces the table in Dembelé-Freitas-Voight.

```
> PS, SCU, SCR, Ex8, Ex24 := InTypes(Q2);
> InTypesSummary(PS, SCU, SCR, Ex8, Ex24);
========================================
    Computed Inertia Types : Summary
========================================

PrincipalSeries  : 5
SCU              : 6
SCR              : 6
Ex8              : 0
Ex24             : 8
----------------------------------------
Total inertial types : 25

------------------------------------------------------------
e   v(N)  Character order  Description               Count  
------------------------------------------------------------
2   4     2                principal series          1      
2   6     2                principal series          2      
3   2     3                supercuspidal unramified  1      
4   8     4                principal series          2      
4   8     4                supercuspidal unramified  2      
6   4     6                supercuspidal unramified  1      
6   6     6                supercuspidal unramified  2      
8   5     4                supercuspidal ramified    2      
8   6     4                supercuspidal ramified    2      
8   8     4                supercuspidal ramified    2      
24  3     4                exceptional, SL(2,3)      1      
24  4     4                exceptional, SL(2,3)      1      
24  6     4                exceptional, SL(2,3)      2      
24  7     4                exceptional, SL(2,3)      4      
------------------------------------------------------------
```

## Implementation details

- The computation of types is based on the computation of the underlying inertia characters, in their avatar as characters of the units of a quotient of a ring of integers. The conditions in [CMFF26] are translated to conditions on the characters to be computed. Hence the computation is reduced to finding q-power-order characters of finite abelian groups (for a prime q) with restrictions, which is essentially a linear algebra problem. The implementation is found in ```package/characters.m```.

## TODO

- [x] Match triplys
- [x] Implement user interfaces
- [x] Uniformize output of exceptionals
- [x] Inertia fields
- [x] Basic documentation
- [x] Pretty print
- [x] Compute all inertial types of all quadratic and cubics and make table of timings
- [ ] Tables for extensions of Q3
- [ ] Stress test with an extension of Q3
- [x] Fast inertia fields for triplys and exceptionals (isolated)
- [x] InertialTypes/InFields -> InTypes/InFields
- [x] Save fields in triplys
- [ ] Group triplys by inducing fields in summary table
- [ ] Print cubic and quadratics in exceptional summary
- [ ] Website with tables

### Future work

- [ ] Intrinsics should admit a list of target conductors (and optimize the computation accordingly)
- [ ] Reconstruction of an inertia type from a given inertia field
- [ ] Detection of base change types
- [ ] InFieldsTwist with arbitrary precision & put it in ExceptionalTypes

## Bugs

## Citation

If you use this package in your research, please cite: _____.