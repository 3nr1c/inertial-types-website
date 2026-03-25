# inertial-types

Magma package to compute inertial types attached to elliptic curves over finite extensions of Qp.

## TODO

- [x] Match triplys
- [x] Implement user interfaces
- [x] Uniformize output of exceptionals
- [x] Inertia fields
- [ ] Documentation
- [x] Pretty print
- [ ] Compute all inertial types of all quadratic and cubics and make table of timings

### Future work

- [ ] Intrinsics should admit a list of target conductors (and optimize the computation accordingly)

## Bugs

- Execute example Q2.m, then ask for InertiaField(Ex24[1,1]);.

```
Runtime error: PrincipalUnitGroup: ERROR in discrete logarithm (quadratic).
```


## Quick start

To use the package you may simply attach our spec:

```magma
AttachSpec("path/to/this/repo/spec");
```

A few basic examples have been provided. For instance, we may compute all inertial types over the field Q4:

```magma
AttachSpec("../spec");

SetVerbose("ECITypes", true);

Q2 := pAdicField(2, 100);
Q4 := UnramifiedExtension(Q2, 2);

Twist, PS, SCU, SCR, Ex8, Ex24 := InertialTypes(Q4);
``` 

The outputs of ```InertialTypes``` are documented in the sections below. Inertial types have some attributes that can be accessed:

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