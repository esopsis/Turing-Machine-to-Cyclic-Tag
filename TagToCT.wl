(* ::Package:: *)

(*This code is a slightly modified version of code here: 
S. Wolfram, A  New  Kind  of  Science, Champaign, IL: Wolfram Media, Inc., 2002 pp. 1113.*)


BeginPackage["TagToCT`"]


Tag1ToCT::usage="Tag1ToCT[{n, substitutions}] converts an n tag system with subsitutuions substitutuion rule that 
	depends only on its first argument to a cyclic tag system."
Tag1ToCTInit::usage="Tag1ToCTInit[init, substitutions] converts the input and the substitutuion rule for a tag system 
	that depends only on its first argument to the input for a cyclic tag system."


Begin["Private`"]


u[i_Integer, k_Integer] := Table[If[j == i + 1, 1, 0], {j, k}]

v[l_List, k_Integer] := Flatten[u[#, k]& /@ l]

Tag1ToCTI[{n_Integer, subs:{(_Integer -> {___Integer})...}}] :=
    With[{k = Length[subs]},
        Join[
			ResourceFunction["ParallelMapMonitored"][
				v[Last[#], k]&, 
				SortBy[subs, First]], 
			Table[{}, {k (n - 1)}]]]

tag1RuleToIntPart[lhs_ -> rhs_List, replacer_] := Replace[lhs, replacer] -> (Replace[#, replacer]& /@ rhs)

getTagSymbolsPart[s_ -> {sp___}] := {s, sp}

getTagSymbols[subs_List] := Catenate[getTagSymbolsPart /@ subs]

intReplacer[symbols_List] :=
    With[{intOrNot = Replace[
			GroupBy[DeleteDuplicates[symbols], IntegerQ], 
			{<|True -> {ints__}|> :> <|False -> {}, True -> {ints}|>, 
				<|False -> {others__}|> :> <|False -> {others}, True -> {0}|>}]},
        MapIndexed[#1 -> First[#2] + Max[intOrNot[True]]&, 
			intOrNot[False]]]

tag1RuleToInt[subs_List] :=
    With[{replacer = intReplacer[getTagSymbols[subs]]},
        ResourceFunction["ParallelMapMonitored"][tag1RuleToIntPart[#, replacer]&, subs]]

Tag1ToCT[{n_Integer, subs:{(_ -> _List)...}}] := Tag1ToCTI[{n, tag1RuleToInt[subs]}]


Tag1ToCTInitI[init:{___Integer}, subs:{(_Integer -> {___Integer})...}] := v[init, Length[subs]]

tag1InitToInt[init_List, subs_List] := Replace[init, intReplacer[getTagSymbols[subs]], {1}]

Tag1ToCTInit[init_List, subs:{(_ -> _List)...}] := Tag1ToCTInitI[tag1InitToInt[init,subs], tag1RuleToInt[subs]]


End[]
EndPackage[]
