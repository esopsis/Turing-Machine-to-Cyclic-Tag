(* ::Package:: *)

(*This package was written by Eric James Parfitt, epartitt84@gmail.com, and based off an algorithm described here: 
Cook, Matthew. \[OpenCurlyDoubleQuote]A Concrete View of Rule 110 Computation.\[CloseCurlyDoubleQuote] CSP (2008). 
and Here: 
T. Neary, D. Woods, P-completeness of cellular automaton rule 110, Lecture Notes in Computer Science 4051
	(2006) 132\[Dash]143.*)


BeginPackage["CWTMToTag`"]


CWTMToTag::usage="CWTMToTag[rules] converts a binary clockwise Turing machine that adds up to two new symbols each step into a Tag system."
CWTMToTagInit::usage="TMToCWTMInit[init] converts the input for a binary clockwise Turing machine that adds up to two new symbols each step to the input for a Tag system."


Begin["Private`"]


compactRules = {{"H" -> "H-", "h" -> "-H-", "A" -> "AA", "B" -> "BB", "C"
     -> "CC", "D" -> "DD", "U" -> "U", "u" -> "V", "X" -> "XX", "x" -> "YY", "V"
     -> "V", "Y" -> "YY"}, {"H" -> "Hh", "A" -> "Aa", "B" -> "Bb", "C" -> "Cc",
     "D" -> "Dd", "U" -> "UuXx", "V" -> "VvYy", "X" -> "Xx", "Y" -> "Yy"}, {"H"
     -> "H-", "A" -> "Aa0", "B" -> "Bb0", "C" -> "CC", "D" -> "DD", "U" -> "UU",
     "V" -> "VV", "X" -> "XX", "Y" -> "YY"}, {"H" -> "Hh", "A" -> "AA", "a" -> 
    "CC", "B" -> "BB", "b" -> "DD", "C" -> "CC", "D" -> "DD", "U" -> "Uu", "V"
     -> "VV", "X" -> "Xx", "Y" -> "YY"}, {"h" -> "", "a" -> "-P-", "b" -> "-Q-",
     "c" -> "A-", "d" -> "B-", "u" -> "", "v" -> "", "x" -> "Ux", "y" -> "Vy"},
     {"P" -> "P-", "Q" -> "Q", "A" -> "Aa", "B" -> "Bb", "U" -> "Uu", "V" -> "Vv"
    }, {"P" -> "[AaBb]H-", "Q" -> "[AaBb]-H-", "A" -> "AA", "a" -> "AA", "B" 
    -> "BB", "b" -> "BB", "U" -> "U[U]", "u" -> "U[U]", "V" -> "U", "v" -> "U"}
    }; 

numberizePt[s_String, stage_Integer, headState_] :=
    Replace[s, {"-" -> "$", "0" -> 0, x_ :> Subscript[x, stage,
         headState]}]

numberize[lhs_String -> rhs_String, {stageIn_Integer, headStateIn_}, {
    stageOut_Integer, headStateOut_}, exceptions : {_String...} : {}] :=
    numberizePt[lhs, stageIn, headStateIn] -> (Characters[rhs] /. {x:(Alternatives
         @@ exceptions) :> numberizePt[x, stageIn, headStateIn], x_String :> numberizePt[
        x, stageOut, headStateOut]})

numberize[rules:{(_String -> _String)...}, in:{stageIn_Integer, headStateIn_
    }, out:{stageOut_Integer, headStateOut_}, exceptions : {_String...} :
     {}] :=
    numberize[#, in, out, exceptions]& /@ rules

stringExcept[p_] :=
    _?(!StringMatchQ[#, p]&)

stringExcept[c_, p_] :=
    _?(StringMatchQ[#, c] && !StringMatchQ[#, p]&)

up6s = Cases[compactRules[[7]], x:(y:stringExcept["P" | "Q"] /; UpperCaseQ[
    y] -> _) :> x]

{"A" -> "AA", "B" -> "BB", "U" -> "U[U]", "V" -> "U"}

down6s = Cases[compactRules[[7]], x:(y:stringExcept["P" | "Q"] /; LowerCaseQ[
    y] -> _) :> x]

{"a" -> "AA", "b" -> "BB", "u" -> "U[U]", "v" -> "U"}

modify6sPart[headState_, rule:{({_, _Integer} -> {_, {___Integer}})...
    }, which6S:{(_String -> _String)..}, letter_String, symbol:(0 | 1)] :=
    numberize[
        Append[
            which6S[[{1, 2, 4}]]
            ,
            letter ->
                "U" <>
                    If[Length[Last[Replace[{headState, symbol}]]] == 2,
                        
                        "U"
                        ,
                        ""
                    ]
        ]
        ,
        {6, headState}
        ,
        {3, First[Replace[{headState, symbol}, rule]]}
    ]

modify6s[headState_, rule:{({_, _Integer} -> {_, {___Integer}})...}, upDown
    :("up" | "down")] :=
    modify6sPart[headState, rule, ##]& @@ Replace[upDown, {"up" -> {up6s,
         "U", 0}, "down" -> {down6s, "u", 1}}]

ruleP = {({_, _Integer} -> {_, {___Integer}})...}; 

tMRule[headState_, rule:ruleP, input:0 | 1] :=
    If[MatchQ[{headState, input}, Alternatives @@ (First /@ rule)],
        numberize[
            Switch[input,
                0,
                    compactRules[[7, 1]]
                ,
                1,
                    compactRules[[7, 2]]
            ] /. (x_ -> y_) :> x -> StringReplace[y, "[" ~~ __ ~~ "]"
                 :> boolToCell[Last[#]]]
            ,
            {6, headState}
            ,
            {3, First[#]}
            ,
            Characters["AaBb"]
        ]&[Replace[{headState, input}, rule]]
        ,
        {}
    ]

newCellP = {Repeated[(0 | 1), {1, 2}]}; 

boolToCell[x:newCellP] :=
    StringJoin[x /. {0 -> "Aa", 1 -> "Bb"}]

rulePt[headState_, rule:ruleP] :=
    {MapAt[Join[#[[ ;; -3]], {Subscript["x", 4, headState] -> {Subscript[
        "U", 5, headState], Subscript["x", 4, headState]}, Subscript["y", 4, headState
        ] -> {Subscript["V", 5, headState], Subscript["y", 4, headState]}}]&, 4][MapThread[
        numberize[#1, Sequence @@ #2]&, {Most[Permute[Most[compactRules], {2,
         3, 6, 1, 4, 5}]], Table[{{n, headState}, {n + 1, headState}}, {n, 5}
        ]}]], numberize[compactRules[[3]], {4, headState}, {1, headState}], modify6s[
        headState, rule, #]& /@ {"up", "down"}, tMRule[headState, rule, 0], tMRule[
        headState, rule, 1]}

getHeadStates[rule:ruleP] :=
    Union[Catenate[{#[[1, 1]], #[[2, 1]]}& /@ rule]]

CWTMToTag[rule:ruleP] :=
    Prepend[0 -> {}][Flatten[rulePt[#, rule]& /@ getHeadStates[rule]]]


firstOvershoot[f_, overshoot_Integer] :=
    Module[{i = 0},
        While[True, If[# > overshoot,
            Return[#]
            ,
            i++
        ]&[f[i]]]
    ]

counterSymbols[l_List] :=
    Catenate[Table[{"U", "u"}, firstOvershoot[2^#&, Length[l]]]]

CWTMToTagInit[{head_, l:{(0 | 1)...}}] :=
    Subscript[#, 2, head]& /@ Join[{"H", "h"}, First[#], counterSymbols[l
        ], Catenate[Rest[#]]]&[l /. {0 -> {"A", "A"}, 1 -> {"B", "B"}}]


End[]


EndPackage[]
