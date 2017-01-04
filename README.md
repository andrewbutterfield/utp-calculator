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
3. From within the interpreter just use `:l ModuleName`, where ModuleName is one of the following:
  1. `Views` - an inital UTP semantics for the basline Command language in the POPL13 Views paper.
  2. `UTCPLaws` - UTP semantics for Unifying Theories of COncurrent Programming
  3. Root - revisiting the semantics in `Views`/`UTCPLaws` with a simpler label generation scheme
  4. `RGAlgebra` - axiomatising the Rely/Guarantee Algebra presented by Ian Hayes at. al at FM2016 in Cyprus.

At the time of writing, `Views` and `UTCP*` are deprecated whilst `Root` and `RGAlgebra` are current.



### Contribution guidelines ###

This repo will not accept outside contributions.
The new `proglogcalc` repo will.

### Who do I talk to? ###

* Repo owner : andrewbutterfield