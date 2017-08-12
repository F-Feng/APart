(* ::Package:: *)

(* ::Subsection::Closed:: *)
(*InnerApart*)


Clear[CachedNullSpace];
CachedNullSpace[pcs_,cs_]:=Module[{ns,tmp1,tmp2},
ns=NullSpace[Transpose@pcs]//Factor;
If[Length[ns]<1,Return[False];];
ns=Sort[ns,Count[#1,0]>=Count[#2,0]&];
ns=First[ns];
CachedNullSpace[pcs,cs]=ns;
Clear[tmp1,tmp2];
Return[ns];
];


Clear[CachedDot];
CachedDot[a_,b_]:=CachedDot[a,b]=a.b//Factor;
Clear[CachedNsNp];
CachedNsNp[ns_,np_]:=CachedNsNp[ns,np]=Apply[And,Map[(#<0)&,Part[Transpose@DeleteCases[{ns,np}//Transpose,p_List/;Part[p,1]===0],2]]];


InnerCollectFunction=Factor;


ClearAll[ApartIR];
ApartIR/:MakeBoxes[ApartIR[pcs_List,cs_List,np_List,vars_List],TraditionalForm]:=With[{exp=Apply[Times,(Defer[Evaluate[#]]&/@(Map[(#.vars)&,pcs]+cs))^np]},RowBox[{"\[LeftDoubleBracketingBar]",MakeBoxes[exp,TraditionalForm],"\[RightDoubleBracketingBar]"}]];


ApartIRSort[exp_,sortFunc_:PcsCsNpSort]:=exp/.ApartIR[pcs_,cs_,np_,vars_]:>ApartIR[Sequence@@sortFunc[pcs,cs,np],vars];


PcsCsNpSort[pcs_List,cs_List,np_List]:=PcsCsNpSort[pcs,cs,np]=Transpose@Sort[Transpose[{pcs,cs,np}],Function[{x,y},Order[Part[x,1],Part[y,1]]>0]]


Clear[InnerApart,CachedApart];
ClearCachedApart[]:=Clear[CachedApart];


ApartNull::usage="ApartNull=1 @ Integrand; ApartNull=0 @ Loop Integral";
InnerApart[pcs_List,cs_List,np:{0...},vars_List]:=ApartNull;
InnerApart[pcs_List,cs_List,np:{___,0,___},vars_List]:=InnerApart[Sequence@@Transpose@DeleteCases[{pcs,cs,np}//Transpose,p_List/;Part[p,3]===0],vars];


InnerApart[xpcs_List,xcs_List,xnp_List,vars_List]:=Module[{lnp,VF,in,tmp,ns,res,p,pcs,cs,np},
{pcs,cs,np}=PcsCsNpSort[xpcs,xcs,xnp];
If[Head[CachedApart[pcs,cs,np,vars]]=!=CachedApart,Return[CachedApart[pcs,cs,np,vars]];];
ns=CachedNullSpace[pcs,cs];
If[ns===False,
tmp=ApartIR[pcs,cs,np,vars];
CachedApart[pcs,cs,np,vars]=tmp;
Clear[lnp,VF,in,ns,res,p,pcs,cs,np];
ClearSystemCache[];
Return[tmp];
];
(*-------------------------------------------------------------------------------*)
(*Print[ns];*)
(*-------------------------------------------------------------------------------*)
If[CachedNsNp[ns,np],
res=CachedDot[ns,cs];
If[res===0,
p=First[FirstPosition[ns,pa_/;pa=!=0,{1},Heads->False]];
tmp=Table[Block[{lnp=np},If[in==p,0,
If[Part[ns,in]===0,0,Part[lnp,p]--;Part[lnp,in]++;-Part[ns,in]/Part[ns,p] InnerApart[pcs,cs,lnp,vars]]
]],{in,Length[ns]}];
tmp=Collect[Plus@@tmp,_ApartIR,InnerCollectFunction];
CachedApart[pcs,cs,np,vars]=tmp;
Clear[lnp,VF,in,ns,res,p,pcs,cs,np];
ClearSystemCache[];
Return[tmp];
];
(*Else Part*)
tmp=Table[Block[{lnp=np},
If[Part[ns,in]===0,0,Part[lnp,in]++;Part[ns,in]/res InnerApart[pcs,cs,lnp,vars]]
],{in,Length[ns]}];
tmp=Collect[Plus@@tmp,_ApartIR,InnerCollectFunction];
CachedApart[pcs,cs,np,vars]=tmp;
Clear[lnp,VF,in,ns,res,p,pcs,cs,np];
ClearSystemCache[];
Return[tmp];
];
(*-------------------------------------------------------------------------------*)
p=First[FirstPosition[np,pa_/;pa>0,{1},Heads->False]];
If[Part[ns,p]===0,
tmp=Block[{lnp=np},Part[lnp,p]=0;InnerApart[pcs,cs,lnp,vars]];
tmp=tmp/.ApartIR[ypcs_,ycs_,ynp_,_]:>InnerApart[Prepend[ypcs,Part[pcs,p]],Prepend[ycs,Part[cs,p]],Prepend[ynp,Part[np,p]],vars];
tmp=Collect[tmp,_ApartIR,InnerCollectFunction];
CachedApart[pcs,cs,np,vars]=tmp;
Clear[lnp,VF,in,ns,res,p,pcs,cs,np];
ClearSystemCache[];
Return[tmp];
];
(*Else Part*)
res=CachedDot[ns,cs];
tmp=Table[Block[{lnp=np},Part[lnp,p]--;If[in==p,If[res===0,0,res/Part[ns,p] InnerApart[pcs,cs,lnp,vars]],Part[lnp,in]++;
If[Part[ns,in]===0,0,-Part[ns,in]/Part[ns,p] InnerApart[pcs,cs,lnp,vars]]
]],{in,Length[ns]}];
tmp=Collect[Plus@@tmp,_ApartIR,InnerCollectFunction];
CachedApart[pcs,cs,np,vars]=tmp;
Clear[lnp,VF,in,ns,res,p,pcs,cs,np];
ClearSystemCache[];
Return[tmp];
];


(* ::Subsection:: *)
(*InnerLog & ApartParse*)


Clear[InnerLog];
InnerLog[x_ y_]:=InnerLog[x]+InnerLog[y];
InnerLog[Power[x_,y_Integer]]:=y InnerLog[x];


ClearAll[FactorWithSign,ApartVars];
SignVars::usage="SignVars->{vars} is an Options of ApartVars";
VarsSign::usage="VarsSign->1 or -1 is an Options of ApartVars";
Options[ApartVars]={SignVars->{},VarsSign->-1};
FactorWithSign[exp_,OptionsPattern[ApartVars]]:=Block[{tmp,pi,sign},
tmp=Map[Coefficient[exp,#]&,OptionValue[SignVars]];
If[Length[DeleteCases[tmp,0]]==0,Return[1]];
pi=First[FirstPosition[tmp,Except[0],Heads->False]];
sign=OptionValue[VarsSign];
If[Head[sign]===List,sign=sign[[pi]]];
Return[tmp[[pi]] sign];
];
DV0FactorWithSign=DownValues[FactorWithSign];
ResetFactorWithSign[]:=(DownValues[FactorWithSign]=DV0FactorWithSign);


Clear[ApartAll];
ApartAll[exp_Plus,vars_List]:=Module[{VF},Distribute[VF[exp]]/.VF[x_]:>ApartAll[x,vars]];
ApartAll[exp_,vars_List]:=Module[{tmp,logs,VF},
tmp=InnerLog[Factor[exp]];
logs=Union[Cases[tmp,_InnerLog,{0,Infinity}]]/.InnerLog->Identity;
Scan[Function[x,If[Not[PolynomialQ[x,vars]||FreeQ[x,Alternatives@@vars]],Print["Error: ",x," is not Polynomial of ",vars];Abort[]]],logs];
Scan[Function[x,If[Length[Normal[CoefficientArrays[x,vars]]]>2,Print["Error: ",x," is not Linear Polynomial of ",vars];Abort[]]],logs];
tmp=Distribute[VF[tmp]]/.VF[c_. InnerLog[y_]]:>c (VF[y/FactorWithSign[y]//Factor]+InnerLog[FactorWithSign[y]]);
On[Assert];Assert[FreeQ[tmp,_FactorWithSign]];
tmp=tmp/.InnerLog[1]->0/.VF[x_]:>InnerLog[Hold[x]];
tmp=Collect[tmp,_InnerLog];
tmp=tmp/.c_. InnerLog[y_]:>VF[Normal@CoefficientArrays[ReleaseHold[y],vars],c];
tmp=tmp/.c_. VF[y_,n_]:>VF[y, c n];
On[Assert];Assert[Factor[tmp-(Plus@@Cases[tmp,_VF,{0,Infinity}])]===0];
tmp=Cases[tmp,_VF,{0,Infinity}];
tmp=tmp/.VF[p_List,np_]:>{If[Length[p]<2,Array[0&,Length[vars]],Part[p,2]],Part[p,1],np};
tmp=Transpose[tmp];
tmp=Append[tmp,vars];
tmp=InnerApart@@tmp;
Clear[logs,VF];
ClearSystemCache[];
Return[tmp];
];


(* ::Subsection::Closed:: *)
(*Some Auxiliary Function*)


Clear[ApartUnion];
ApartUnion[exp_]:=Cases[exp,_ApartIR,{0,Infinity}]//Union;


Clear[ApartRules];
ApartRules[aparts_List]:=Module[{tmp,tmp2,rules={},VF,res},
tmp=aparts/.ApartIR->List;
tmp=Map[Function[arg,Thread[VF[arg[[1]],arg[[2]]]]/.VF->Append],tmp];
tmp=tmp//Union;
tmp=SortBy[tmp,Length];
Scan[Function[in,
tmp2=SelectFirst[tmp[[in+1;;]],Function[x,SubsetQ[x,tmp[[in]]]]];
If[Head[tmp2]=!=Missing,AppendTo[rules,VF[tmp[[in]]]->VF[tmp2]]];
],Range[Length[tmp]-1]];
tmp=rules/.HoldPattern[VF[x_]->VF[y_]]:>(VF[x]->(VF[y]//.rules));
tmp=tmp/.HoldPattern[VF[x_]->VF[y_]]:>(VF[x]->VF[Complement[y,x]]);
rules=Dispatch[tmp];
res=aparts/.air:ApartIR[pcs_,cs_,ns_,vars_]:>(
tmp2=Thread[VF[pcs,cs]]/.VF->Append;
tmp=VF[tmp2]/.rules/.VF->Identity;
If[tmp2=!=tmp,
tmp2={pcs,cs,PadRight[ns,Length[tmp]+Length[ns]],vars};
Scan[Function[ele,AppendTo[tmp2[[1]],ele[[;;-2]]];AppendTo[tmp2[[2]],ele[[-1]]];],tmp];
Part[tmp2,1;;3]=Apply[PcsCsNpSort,Part[tmp2,1;;3]];
ApartIR@@tmp2,
air]);
Clear[tmp,tmp2,rules,VF];
Return[res];
];


Clear[ApartComplete];
ApartComplete[exp_ApartIR,OptionsPattern[ApartVars]]:=Module[{tmp,tmp2,in,vars,subs={}},
tmp=exp/.ApartIR->List;
vars=Part[tmp,4];
If[Length[OptionValue[SignVars]]>0&&OptionValue[VarsSign]<0,subs=Thread[OptionValue[SignVars]->(-OptionValue[SignVars])]];
If[Length[Part[tmp,1]]>=Length[vars],Return[exp]];
For[in=1,in<=Length[vars],in++,
tmp2=Part[Normal@CoefficientArrays[Part[vars/.subs,in],vars],2];
If[MatrixRank[Join[Part[tmp,1],{tmp2}]]>Length[Part[tmp,1]],
AppendTo[Part[tmp,1],tmp2];
AppendTo[Part[tmp,2],0];
AppendTo[Part[tmp,3],0];
If[Length[Part[tmp,1]]>=Length[vars],Break[];];
];
];
Part[tmp,1;;3]=Apply[PcsCsNpSort,Part[tmp,1;;3]];
Return[ApartIR@@tmp];
];


ApartComplete[exp_]:=exp/.a_ApartIR:>ApartComplete[a];


RemoveApart[exp_]:=exp/.ApartIR[pcs_,cs_,np_,vars_]:>Apply[Times,(Map[(#.vars)&,pcs]+cs)^np];


FireArguments[ApartIR[pcs_,cs_,np_,vars_],p2pn_:Identity]:=FireArguments[ApartIR[pcs,cs,np,vars],p2pn]=Sequence[p2pn[Map[(#.vars)&,pcs]+cs],-np];


(* ::Subsection::Closed:: *)
(*Mathematica 9 & Below*)


If[Head[FirstPosition[{1, 1}, 1]]===FirstPosition,FirstPosition[x___]:=First[Position[x]]];
