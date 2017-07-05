The main Idea of this project is: Find ways for correcting non-SyntaxQ expressions to SyntaxQ expressions. 

As example: we have this string: `"Fold[Plus,a,{b,c,d,e}]". We can remove it one character from this string and get a `StringLength["Fold[Plus,a,{b,c,d,e}]"]` different strings. We can get it by

    inp = "Fold[Plus,a,{b,c,d,e}]";
    StringDrop[inp, {#}] & /@ Range[StringLength[inp]]



So, it will 22 different strings:

`old[Plus,a,{b,c,d,e}]
Fld[Plus,a,{b,c,d,e}]
...
Fold[Plus,a,{b,c,d,e]
Fold[Plus,a,{b,c,d,e}`

Some of them will give us `True` for function `SyntaxQ`. Let's try sort it by `Select`:

    dropped = StringDrop[inp, {#}] & /@ Range[StringLength[inp]]
    Select[dropped, Not[SyntaxQ[#]] &]

And we got only 4 results from 22:

`FoldPlus,a,{b,c,d,e}]
Fold[Plus,a,b,c,d,e}]
Fold[Plus,a,{b,c,d,e]
Fold[Plus,a,{b,c,d,e}
`

Let's try to evaluate it by function `ToExpression`.

    Map[ToExpression, Select[dropped, Not[SyntaxQ[#]] &]]

And we get list of errors:

`{$Failed, $Failed, $Failed, $Failed}`

It means that code are not correct, but it will be necessary to check `ToExpression` on not filtered list of strings:

    Map[ToExpression, dropped]

`{old[Plus,a,{b,c,d,e}]
Fld[Plus,a,{b,c,d,e}]
Fod[Plus,a,{b,c,d,e}]
Fol[Plus,a,{b,c,d,e}]
$Failed
lus[lus[lus[lus[a,b],c],d],e]
Pus[Pus[Pus[Pus[a,b],c],d],e]
Pls[Pls[Pls[Pls[a,b],c],d],e]
Plu[Plu[Plu[Plu[a,b],c],d],e]
Plusa[Plusa[Plusa[b,c],d],e]
b+c+d+e+Null
a b+a c+a d+a e
$Failed
a+c+d+e+Null
a+bc+d+e
a+b+d+e+Null
a+b+cd+e
a+b+c+e+Null
a+b+c+de
a+b+c+d+Null
$Failed
$Failed`

As we see, some of them were evaluated without any errors. It is normal because of `old, Fld, Fod, Fol, etc.,` counts as non defined functions. `Null` also counts as argument of function. It is the main reason of filtering the *dropped* list of strings. Next step of this topic is the finding way of correction our strings. The general way to correction is defining of missing character and adding it in every place of our string. Then we must check all our new inputs for Syntax corectness.
Inserting of missed character, general way:

    correctInserting[str_String, strinst_String] :=
     Module[{s = str, s1, s2, result = {}, i, symb = strinst},
      s1 = StringSplit[str, x : PunctuationCharacter :> x];
      For[
       i = 1, i <= Length[s1], i++,
       If[
        Not[MemberQ[$SystemSymbols, s1[[i]]]],
        s2 =
         {# + Total[StringLength[#] & /@ (s1[[1 ;; i - 1]])],
            StringInsert[s1[[i]], symb, {#}]} &
          /@ Range[StringLength[s1[[i]]] + 1];
        AppendTo[
         result, {s2[[#, 1]], {s1[[1 ;; i - 1]], s2[[#, 2]], 
             s1[[i + 1 ;;]]}} & /@ Range[StringLength[s1[[i]]] + 1]]
        ]
       ];
      DeleteDuplicates[Transpose[{Transpose[Flatten[result, 1]][[1]],
         StringJoin /@ Transpose[Flatten[result, 1]][[2]]}]]

So, this function won't insert character into functions which are in:

    Names["System`*"]

I tried 2 approaches: using of string patterns and using internal service of Mathematica for checking the errors. During my work in WSS2017 I chosed the second way. But let's explain why? I will show the last version of string patterns system of this:

    syntaxCorrector[str_String] :=
     Module[
      {inp = str, result = {}, openbrack, closebrack, openbrace, 
       closebrace, openparen, closeparen},
      openbrack = StringCount[str, {"["}];
      closebrack = StringCount[str, {"]"}];
      openbrace = StringCount[str, {"{"}];
      closebrace = StringCount[str, {"}"}];
      openparen = StringCount[str, {"("}];
      closeparen = StringCount[str, {")"}];
      Which[
       Not[openbrack == closebrack],
       If[
         openbrack > closebrack,
         AppendTo[result, "Closing Bracket Missed"];
         (*Close Bracket Inserting*)
         s1 = 
          Table[{i, StringInsert[str, "]", i]}, {i, 1, 
            StringLength[str] + 1}];
         (*Selecting the True for SyntaxQ*)
         s2 = Select[s1, SyntaxQ[#[[2]]] &];
         (*Decomposition of expression*)
         s3 = analyser /@ Last[Transpose[s2]];
         s4 = DeleteDuplicates@Flatten@s3;
         AppendTo[result, Column[Flatten[{"Possible solutions", s4}]]];
         ,
         AppendTo[result, "Opening Bracket Missed"];
         (*Open Bracket Inserting*)
         s1 = 
          Table[{i, StringInsert[str, "[", i]}, {i, 1, StringLength[str]}];
         (*Selecting the True for SyntaxQ*)
         s2 = Select[s1, SyntaxQ[#[[2]]] &];
         (*Splitting for finding the correct names of functions*)
         s31 = 
          Table[Flatten[{s2[[i, 1]] - 1, 
             StringSplit[
              StringTake[s2[[i, 2]], s2[[i, 1]]], {"[", ","}]}], {i, 1, 
            Length[s2]}];
         s32 = 
          Table[Flatten[{s2[[i, 1]] - 1, 
             StringSplit[StringTake[s2[[i, 2]], s2[[i, 1]]], 
              x : "[" :> x]}], {i, 1, Length[s2]}];
         (*Checking names for correctness by SystemNames*)
         s4 = 
          Sort[GroupBy[s31, ContainsAny[Names["System`*"], {Last[#]}] &]];
         (*Getting the correct inserts numbers*)
         s5 = Map[First, Values[s4][[1]]];
         (*From the list of inserting we choose those, 
         which have a number in s4*)
         s6 = Select[s32, ContainsAny[{First[#]}, s5] &];
         (*Constructing the text cell*)
         s7 = 
          DeleteDuplicates[
           StringJoin[{#[[2 ;; -1]], StringDrop[str, First[#]]}] & /@ s6];
         AppendTo[result, Column[Flatten[{"Possible solutions", s7}]]];
         ];
       ,
       Not[StringCount[str, {"{"}] == StringCount[str, {"}"}]],
       If[
         openbrace > closebrace,
         AppendTo[result, "Closing Braces Missed"];
         s1 = 
          Table[StringInsert[str, "}", i], {i, 1, StringLength[str] + 1}];
         s2 = DeleteDuplicates@Select[s1, SyntaxQ];
         AppendTo[result, Column[Flatten[{"Possible solutions", s2}]]];
         ,
         AppendTo[result, "Opening Braces Missed"];
         s1 = 
          Table[StringInsert[str, "{", i], {i, 1, StringLength[str] + 1}];
         s2 = DeleteDuplicates@Select[s1, SyntaxQ];
         AppendTo[result, Column[Flatten[{"Possible solutions", s2}]]];
         ];
       ,
       Not[StringCount[str, {"("}] == StringCount[str, {")"}]],
       If[
         openparen > closeparen,
         AppendTo[result, "Closing Parenthes Missed"];
         s1 = 
          Table[StringInsert[str, ")", i], {i, 1, StringLength[str] + 1}];
         s2 = DeleteDuplicates@Select[s1, SyntaxQ];
         AppendTo[result, Column[Flatten[{"Possible solutions", s2}]]];
         ,
         AppendTo[result, "Opening Parenthes Missed"];
         s1 = 
          Table[StringInsert[str, "(", i], {i, 1, StringLength[str] + 1}];
         s2 = DeleteDuplicates@Select[s1, SyntaxQ];
         AppendTo[result, Column[Flatten[{"Possible solutions", s2}]]];
         ];
       ,
       Not[EvenQ[StringCount[str, "\""]]],
       AppendTo[result, "Quotes Missed"]
       ,
       StringCount[str, {"["}] == StringCount[str, {"]"}] &&
        StringCount[str, {"{"}] == StringCount[str, {"}"}] &&
        StringCount[str, {"("}] == StringCount[str, {")"}] &&
        StringCount[str, {"("}] == StringCount[str, {")"}] &&
        EvenQ[StringCount[str, "\""]],
       s1 = StringSplit[str, {"[", "]", ","}];
       s2 = DeleteCases[Select[Evaluate[s1], Not[SyntaxQ[#]] &], ""];
       s3 = Riffle[StringSplit[str, s2], Style[#, Red] & /@ s2];
       s4 = TextCell[Row[s3]];
       AppendTo[result, s4];
       ];
      Column[result]
      ]

It worked very slow and always I could give input which would not give me correct output:

    Subsets[{a, b, c]

You can look at this pattern system on my [GitHub][1] or by this [directlink][2].
 The second way use `Block` for this fine code:

    messageAnalysis[str_] :=
      Module[{mess, result},
       Block[{$MessageList = {}},
        Quiet[
         ToExpression[str];
         mess = $MessageList;
         ];
        If[mess =!= {}, result = False, result = True];
        ];
       result
       ];

So, If we have any message it will give us `False`. And this function `messageAnalyser` allow to analyse all our construction more precisely.
You can look at 
  [1]: https://github.com/AndreyKrotkikh
  [2]: https://github.com/AndreyKrotkikh/WSS2017/blob/master/SyntaxCorrector.nb
