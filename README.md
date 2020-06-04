# README #

This is a Haskell Library Package for doing UTP semantics calculations, as described in the paper:

Andrew Butterfield, "UTPCalc - A Calculator for UTP Predicates", in Jonathan P. Bowen, Huibiao Zhu (eds.), *6th International Symposium, UTP2016,
Reykjavik, Iceland, June 4-5 2016, Revised Selected Papers*, LNCS 10134, Springer, ppX-X+19, 2017. DOI: 10.1007/978-3-319-52228-9 10

The final uploaded version of the UTP2016 paper, before publisher proofing, is at the `UTP2016-final` tag.

Subsequent commits reflect on-going development
up to the tag `RGAlgebra-0.2`

There is no commit indicated in the repo that matches the calculator example shown in the paper. An attempt was made to find such a commit it seems not to exist.

The general library modules
that make up the calculator have moved to a new location (Github) under a new name:

`proglogcalc` : Programmable Logic Calculator.

This repo has been re-configured to use proglogcalc as a submodule and will continue to be used to support my UTP theory building work. 


### How do I get set up? ###

1. Use git to pull the proglogcalc submodule
2. To build, use `stack ghci`
3. From within the interpreter just use `:l <modname>`, where `<modname>` is one of the following:
  1. `Views` - an inital UTP semantics for the baseline Command language in the POPL13 Views paper.
  2. `UTCPLaws` - UTP semantics for Unifying Theories of Concurrent Programming
  3. `Root` - revisiting the semantics in `Views`/`UTCPLaws` with a simpler label generation scheme
  4. `RGAlgebra` - axiomatising the Rely/Guarantee Algebra presented by Ian Hayes et. al at FM2016 in Cyprus.

At the time of writing, `Views` and `UTCP*` are deprecated whilst `Root` and `RGAlgebra` are current.

#### Working in `Root`

The most useful command to start and run the calculator is `rputcalc`
which takes a predicate as argument, and displays a proof transcript on exit.

For example: `rputcalc aorb` will produce something like:

```
UTP-Calc v0.2, Root 0.3, std-utp 0.2, std 0.2, std-expr 0.1, std-set 0.1, std-pred 0.2
<a> + <b>

... proof steps elided ...

<a> + <b>
 = « Expanded defn. of + »
W(A(r|ii|r1) ∨ A(r|ii|r2) ∨ <a>[r1/r] ∨ <b>[r2/r] ∨ A(r1*|ii|r*) ∨ A(r2*|ii|r*))
 = « Expanded defn. of Atom calculation »
W(
     A(r|ii|r1)
   ∨ A(r|ii|r2)
   ∨ (II ∨ A(r|a|r*))[r1/r]
   ∨ <b>[r2/r]
   ∨ A(r1*|ii|r*)
   ∨ A(r2*|ii|r*)
)
 = « Expanded defn. of Atom calculation »
W(
     A(r|ii|r1)
   ∨ A(r|ii|r2)
   ∨ (II ∨ A(r|a|r*))[r1/r]
   ∨ (II ∨ A(r|b|r*))[r2/r]
   ∨ A(r1*|ii|r*)
   ∨ A(r2*|ii|r*)
)
 = « simplify »
W(
     A(r|ii|r1)
   ∨ A(r|ii|r2)
   ∨ A(r1|a|r1*)
   ∨ A(r2|b|r2*)
   ∨ A(r1*|ii|r*)
   ∨ A(r2*|ii|r*)
)
```

#### Working in `RGAlgebra`

The most useful command to start and run the calculator is `rgcalcput`
which takes a predicate as argument, and displays a proof transcript on exit.

For example: `rgcalcput $ mkSeq [nil,skip,bot,top]` will produce
something like:

```
UTP-Calc v0.2, RGAlgebra 0.4, std-expr 0.1, std-set 0.1, std-pred 0.2
nil ; skip ; ⊥ ; ⊤

... proof steps elided ...

nil ; skip ; ⊥ ; ⊤
 = « ⊥ is left-zero for ; »
nil ; skip ; ⊥
 = « simplify »
skip ; ⊥
```


#### Working in deprecated modules

`Views` - try `vputcalc testpr`

`UTCPLaws` - no calculator available



### Contribution guidelines ###

This repo will not accept outside contributions.
The new `proglogcalc` repo will.

### Who do I talk to? ###

* Repo owner : andrewbutterfield