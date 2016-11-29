\HDRa{Calculator Alphabets}\label{ha:calc-alpha}
\begin{code}
module CalcAlphabets where
import Utilities
import Data.List
import CalcTypes
import CalcPredicates
\end{code}

\HDRb{Alphabet Introduction}\label{hb:alpha-intro}

In most%
\footnote{Some theories, most notably those involving probability,
use non-homogeneous relations, usually relating a starting ``state''
to some final (non-deterministic) set of ``lifted states''.}
mainstream UTP theories,
we find definitions of homogeneous relations
over a collection of observation variables
$v_1,\ldots,v_n$,
where the undashed variables are the before-state of the system,
and their dashed counterparts
$v_1,\ldots,v_n$
denote the after-state.
A distinction is made between observations that correspond
to the values of program variables (``program'' or ``script'')
and those that refer to other observable aspects of program execution
(``auxillary'' or ``model''), as exemplified by the observation $ok$
in the theory of Designs, that captures the notion of a program starting,
and terminating.

In the theory of shared-variable concurrency that drove the need for,
and development of this UTP calculator library,
we found a need to move away from homogeneous relations,
to a more nuanced approach,
that saw some of the model variables
being treated as having no ``after'' observations,
because they in fact represented static parameters that captured,
in a general way,
the context in which any given language construct was embedded.
This enabled the construction of compositional semantic theories
that were also ``context-aware''.

\HDRb{Alphabet Subsets}\label{hb:alpha-subsets}

To support this
we predefine some standard names for important alphabet subsets
($Alf,Obs,Obs',Mdl,Mdl',Scr,Scr',Dyn,Dyn',Stc$):
\begin{code}
aAlf  = "\bAlf"   -- entire alphabet
aObs  = "\bObs"   -- all undashed variables
aObs' = "\bObs'"  -- all dashed variables
aMdl  = "\bMdl"   -- all undashed model variables
aMdl' = "\bMdl'"  -- all dashed model variables
aScr  = "\bScr"   -- all undashed script variables
aScr' = "\bScr'"  -- all dashed script variables
aDyn  = "\bDyn"   -- all undashed dynamic observables
aDyn' = "\bDyn'"  -- all dashed dynamic observables
aStc  = "\bStc"   -- all undashed static parameters
\end{code}

We also need a special way to indicate when substitutability
applies to any variables:

\begin{code}
anyVars = ["*"]
\end{code}

\HDRc{Well-Formed Subsets}\label{hc:alpha-wf-subsets}

A consistent set of the above alphabets should obey the following laws:
\RLEQNS{
   Alf &=& Obs \cup Obs'
\\ Obs &=& Mdl \cup Scr & \mbox{dashed similarly}
\\ Obs &=& Dyn \cup Stc & \mbox{dashed similarly}
\\ \emptyset &=& Mdl \cap Scr & \mbox{dashed similarly}
\\ \emptyset &=& Dyn \cap Stc & \mbox{dashed similarly}
\\ Stc' &=& \emptyset
}
The last law is why we do not provide a\texttt{ Stc'} alphabet entry.

In general we expect the relation to be homogeneous on the dynamic variables
\RLEQNS{
   Dyn' &=& (Dyn)'
}
In most cases, script variables will be dynamic:
\RLEQNS{
   Scr &\subseteq& Dyn & \mbox{dashed similarly}
}



\HDRc{Minimal Definition}\label{hc:alpha-minimal}

A basic minimal definition adhering to all the above rules
consists of disjoint alphabets $Scr$, $nonScrDyn$ and $Stc$
with the following calculations of the rest:
\RLEQNS{
   Scr' &=& (Scr)'
\\ Dyn &=& Scr \cup nonScrDyn
\\ Dyn' &=& (Dyn)'
\\ Mdl &=& nonScrDyn \cup Stc
\\ Mdl' &=& (nonScrDyn)'
}
with $Obs$, $Alf$ etc derived as above.
\begin{code}
stdAlfDictGen :: [String] -> [String] -> [String] -> Dict
stdAlfDictGen scr nonScrDyn stc
 = let
    scr' = map addDash scr
    dyn = scr ++ nonScrDyn
    dyn' = map addDash dyn
    mdl = nonScrDyn ++ stc
    mdl' = map addDash nonScrDyn
    obs = mdl ++ scr
    obs' = mdl' ++ scr'
    alf = obs ++ obs'
   in makeDict $ mapsnd (AlfEntry . sort)
     [ (aAlf, alf)
     , (aObs, obs), (aObs', obs')
     , (aMdl, mdl), (aMdl', mdl')
     , (aScr, scr), (aScr', scr')
     , (aDyn, dyn), (aDyn', dyn')
     , (aStc, stc)
     ]
\end{code}

\HDRc{ Variable Basics}\label{hc:var-basics}
\begin{code}
isDash, notDash :: String -> Bool
isDash v = last v == '\''
notDash v = last v /= '\''

addDash, remDash :: String -> String
addDash v = v ++"'"
remDash = init
\end{code}

\HDRb{Dictionary-based Alphabet Lookup}\label{hb:alpha-lookup}


\HDRc{Total Alphabet Lookup}\label{hc:total-alpha-lookup}

It can be helpful to have total alphabet lookup functions,
returning empty lists if nothing is found:
\begin{code}
getAlpha :: String -> Dict ->[String]
getAlpha alfname d
 = case alookup alfname d of
     Nothing              ->  []
     Just (AlfEntry alf)  ->  alf
\end{code}

\HDRc{Dictionary-based variable properties}\label{hb:var-prop-lookup}

\begin{code}
isStc, isDyn, isDyn', isDynObs, notDynObs :: Dict -> String -> Bool
isStc d v
 = case alookup aStc d of
    Just (AlfEntry alfpart)  ->  v `elem` alfpart
    _                        ->  False
isDyn d v
 = case alookup aDyn d of
    Just (AlfEntry alfpart)  ->  v `elem` alfpart
    _                        ->  False
isDyn' d v
 = case alookup aDyn' d of
    Just (AlfEntry alfpart)  ->  v `elem` alfpart
    _                        ->  False
isDynObs d = isDyn d ||| isDyn' d
notDynObs d = not . isDynObs d
\end{code}

Lifting predicates
\begin{code}
(|||) p q x = p x || q x
(&&&) p q x = p x && q x
\end{code}
