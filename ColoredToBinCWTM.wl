(* ::Package:: *)

(*This package was written by Eric James Parfitt, epartitt84@gmail.com, and based off an algorithm described here: 
	Cook, Matthew. \[OpenCurlyDoubleQuote]A Concrete View of Rule 110 Computation.\[CloseCurlyDoubleQuote] CSP (2008). 
and Here: 
	T. Neary, D. Woods, P-completeness of cellular automaton rule 110, Lecture Notes in Computer Science 4051
		(2006) 132\[Dash]143.*)


BeginPackage["ColoredToBinCWTM`"]


ColoredToBinCWTM::usage = "ColoredToBinCWTM[rules] converts a multi colored clockwise Turing machine rule to a two 
	colored clockwise Turing machine rule."
ColoredToBinCWTMInit::usage = "TMToCWTMInit[init, rule] converts input and a rule for a multi colored clockwise 
	Turing machine to the input for a two colored clockwise Turing machine."
Li::usage = "A List type structure that won't match with ordinary Lists."


Begin["Private`"]


getTapeSyms[{_, a_Integer} -> {_, {aps:Repeated[_Integer, 2]}}] := {a, aps}

maxTapeSym[rule_List] := Max[getTapeSyms /@ rule]

getLast[{{__, y_}}] := {y}

getLast[{{x__}, {y__}}] := {x, y}[[-2 ;; ]]

headToSym[{s_, a_} -> {sp_, aps_}] := (sp -> aps)

headToSyms[head_, rules_List, pad_Integer] :=
    DeleteDuplicates[getLast /@ 
		IntegerDigits[
			ReplaceList[head, headToSym/@ rules], 
			2, pad]]

leftPaddedParition[l_List, n_, pad_:0] :=
    Replace[#, {x_} :> {pad, x}]& /@ 
		Reverse[Reverse /@ Partition[Reverse[l], UpTo[n]]]

getToWrite[aps_List, pad_Integer] :=
    If[Length[aps] == 1,
        List /@ IntegerDigits[First[aps], 2, pad],
        leftPaddedParition[
			Join[
				IntegerDigits[First[aps], 2, pad], 
				IntegerDigits[Last[aps], 2, pad]], 
			2]
    ]

coloredToBinCWTMPart[{s_, a_Integer} -> {sp_, aps:{Repeated[_Integer,2]}}, rules_List] :=
    With[{maxSym = maxTapeSym[rules]},
        With[{pad = Ceiling[Log2[maxSym + 1]]},
            With[{toWrite = getToWrite[aps, pad]},
                Join[
					Table[
						{Li[s, {head}, 
									Most[IntegerDigits[a, 2, pad]]], 
							Last[IntegerDigits[a, 2, pad]]} -> 
								{Li[sp, toWrite, {}], head},
						{head, headToSyms[s, rules, pad]}]
                    ,
                    Catenate[
						Table[
							Table[
								{Li[sp, toWrite[[i ;; ]], Most[read]],
										Last[read]} -> 
									{Li[sp, toWrite[[i + 1 ;; ]], read], toWrite[[i]]},
								{read,
									If[i == pad - 1,
										DeleteDuplicates[Table[
											Most[IntegerDigits[j, 2, pad]], 
											{j, 0, maxSym}]],
										Tuples[{0, 1}, i]]}],
                             {i, pad - 1}]]]]]]

ColoredToBinCWTMI[rule:{({_, _Integer} -> {_, {__Integer}})...}] :=
    DeleteDuplicates[Catenate[coloredToBinCWTMPart[#, rule]& /@ rule]]

intReplacer[symbols_List] :=
    With[{intOrNot = Replace[GroupBy[DeleteDuplicates[symbols], IntegerQ], 
			{<|True -> {ints__}|> :> <|False -> {}, True -> {ints}|>, 
				<|False -> {others__}|> :> <|False -> {others}, True -> {0}|>}]},
        MapIndexed[#1 -> First[#2] + Max[intOrNot[True]]&, 
			intOrNot[False]]]

getRuleSymbols[{_, a_} -> {_, {aps__}}] := {a, aps}

ruleToIntsPart[{s_, a_} -> {sp_, aps_List}, replacer_List] :={s, Replace[a, replacer]} -> {sp, Replace[replacer] /@ aps}

ruleToInts[rule:{({_, _} -> {_, _List})...}] :=ruleToIntsPart[#, intReplacer[Catenate[getRuleSymbols /@ rule]]]& /@
	rule

ColoredToBinCWTM[rule:{({_, _} -> {_, _List})...}] := ColoredToBinCWTMI[ruleToInts[rule]]


coloredToBinCWTMInitPart[{_, as_List}, {sp_, aps_List}] := {Li[sp, getToWrite[aps, pad], {}], as}

coloredToBinCWTMInitPart[{_, as_List}, {sp_, aps_List}, pad_Integer] :=
    With[{toWrite = getToWrite[aps, pad]},
        With[{input = Join[Catenate[IntegerDigits[Rest[as], 2, pad]],
				Catenate[Most[toWrite]]]},
            {Li[sp, {Last[toWrite]}, input[[ ;; pad - 1]]], input[[pad ;;]]}]]

coloredToBinCWTMInitI[init:{s_, {a_Integer, ___Integer}}, rule:{({_,_Integer} -> {_, {__Integer}})...}] :=
    coloredToBinCWTMInitPart[init, Replace[{s, a}, rule], Ceiling[Log2[maxTapeSym[rule] + 1]]]

ColoredToBinCWTMInit[{s_, as_List}, rule_List] :=
    coloredToBinCWTMInitI[{s, Replace[intReplacer[Catenate[getRuleSymbols /@ rule]]] /@ 
			as}, 
		ruleToInts[rule]]


End[]
EndPackage[]
