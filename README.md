# README #

This is a Haskell Library Package for doing UTP semantics calculations, as described in the paper:

Andrew Butterfield, "UTPCalc - A Calculator for UTP Predicates", in Jonathan P. Bowen, Huibiao Zhu (eds.), *6th International Symposium, UTP2016,
Reykjavik, Iceland, June 4-5 2016, Revised Selected Papers*, LNCS 10134, Springer, ppX-X+19, 2017. DOI: 10.1007/978-3-319-52228-9 10

If you want a version of the code compatible with the final version of the UTP2016 paper
then checkout the `UTP2016-final` tag.

Subsequent commits reflect on-going development
up to the tag `RGAlgebra-0.2`

From this point on the general library modules
that make up the calculator are moving to a new location under a new name:

proglogcalc : Programmable Logic Calculator.

This repo will be re-configured to use proglogcalc as a submodule and will continue to be used to support my UTP theory building work. 


### How do I get set up? ###

Simple, go into /src and run:

ghci UTCPCalc.lhs




### Contribution guidelines ###

This repo will not accept outside contributions.
The new proglogcalc repo will.

### Who do I talk to? ###

* Repo owner : andrewbutterfield