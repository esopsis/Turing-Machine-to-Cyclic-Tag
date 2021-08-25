(* ::Package:: *)

(*This package was written by Eric James Parfitt, epartitt84@gmail.com, and based off an algorithm described here: 
Cook, Matthew. \[OpenCurlyDoubleQuote]A Concrete View of Rule 110 Computation.\[CloseCurlyDoubleQuote] CSP (2008). 
and Here: 
T. Neary, D. Woods, P-completeness of cellular automaton rule 110, Lecture Notes in Computer Science 4051
	(2006) 132\[Dash]143.*)


BeginPackage["TMtoCWTM`"]


TMToCWTM::usage = "TMToCWTM[rules] converts an ordinary Turing machine rule to a clockwise Turing machine rule."
TMToCWTMInit::usage = "TMToCWTMInit[init] converts the input for an ordinary Turing machine to the input for a clockwise Turing machine."
Fl::usage = "Fl[stored,changing] is a head wrapper that keeps a stored and changing variable while the Turing machine is moving left."
Fr::usage = "Fr[stored] is a head wrapper that keeps a stored varialbe while the Turing machine is moving further to the right than it has 
	previously."
Ml::usage = "Ml is a tape marker to let the Cyclic Turing machine know when it's looped back around while the Turing machine is moving left."
L::usage = "L is a tape marker corresponding to the first blank cell on the leftmost side of the Turing machine as it has evolved."
R::usage = "R is a tape marker corresponding to the first blank cell on the leftmost side of the Turing machine as it has evolved."


Begin["Private`"]


tMToCWTMPartB[{s_, a_} -> {sp_, ap_, 1}] :=
    {{s, a} -> {sp, {ap}}}

tMToCWTMPartB[{s_, a_} -> {sp_, ap_, -1}] :=
    {{s, a} -> {Fl[sp, ap], {Ml}}}

tMToCWTMPart[rule:({s_, 0} -> {sp_, ap_, 1})] :=
    Join[tMToCWTMPartB[rule], {{s, L} -> {sp, {L, ap}}, {s, R} -> {Fr[
        ap], {Ml, R}}}]

tMToCWTMPart[rule:({s_, 0} -> {sp_, ap_, -1})] :=
    Join[tMToCWTMPartB[rule], {{s, R} -> {Fl[sp, R], {Ml, ap}}, {s, L
        } -> {Fl[sp, ap], {L, Ml}}}]

tMToCWTMPart[rule:({s_, a_} -> {sp_, ap_, _})] :=
    tMToCWTMPartB[rule]

tMToCWTMMarkerChecker[rule:({s_, a_} -> _)] :=
    {Fl[s, a], Ml} -> Replace[{s, a}, tMToCWTMPart[rule]]

tapeSymbols[rules:{({_, _} -> {_, _List})...}] :=
    DeleteDuplicates[Catenate[Replace[({_, s_} -> {_, {sps__}}) :> {s,
         sps}] /@ rules]]

tMToCWTMMarkerChecker[({s_, a_} -> {sp_, {aps__}}), rules_] :=
    Join[{Fl[s, a], #} -> {Fl[s, #], {a}}& /@ DeleteCases[tapeSymbols[
        rules], Ml], {{Fl[s, a], Ml} -> Replace[{s, a}, rules], {Fr[s], a} ->
         {Fr[s], {a}}, {Fr[s], Ml} -> Replace[{s, 0}, rules]}]

TMToCWTM[rule:{({_, _} -> {_, _, _})...}] :=
    With[{nonMarkers = Catenate[tMToCWTMPart /@ rule]},
        Join[nonMarkers, Catenate[tMToCWTMMarkerChecker[#, nonMarkers
            ]& /@ nonMarkers]]
    ]

TMToCWTMInit[{s_, as_List}] :=
    {s, Join[as, {R, L}]}


End[]
EndPackage[]
