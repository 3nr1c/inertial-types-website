# inertial-types

Magma package to compute inertial types attached to elliptic curves over finite extensions of Qp.

## TODO

- [x] Match triplys
- [x] Implement user interfaces
- [x] Uniformize output of exceptionals
- [x] Inertia fields
- [ ] Documentation
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

## Bugs

- [x] Execute example Q2.m, then ask for InertiaField(Ex24[1,1]);.

```
Runtime error: PrincipalUnitGroup: ERROR in discrete logarithm (quadratic).
```
- [x] The function that matches triplys has some bug. To reproduce: go to the intrinsic 
```intrinsic SupercuspidalRamified(F::FldPad : QuadExt := [], Twist := [])``` and uncomment the three ```Remove``` lines towards end of the function.


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

Twist, PS, SCU, SCR, Ex8, Ex24 := InTypes(Q4);
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

## Description of outputs

## Printing summaries

## Citation

If you use this package in your research, please cite: _____.