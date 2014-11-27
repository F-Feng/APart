(* ::Package:: *)

(* ::Subsection:: *)
(*InnerApart*)


Clear[CachedNullSpace];
CachedNullSpace[pcs_,cs_]:=Block[{ns,tmp1,tmp2},
ns=NullSpace[Transpose@pcs]//Factor;
If[Length[ns]<1,Return[False];];
ns=Sort[ns,Count[#1,0]>Count[#2,0]&];
ns=First[ns];
CachedNullSpace[pcs,cs]=ns;
Return[ns];
];


Clear[CachedDot];
CachedDot[a_,b_]:=CachedDot[a,b]=a.b//Factor;
Clear[CachedNsNp];
CachedNsNp[ns_,np_]:=CachedNsNp[ns,np]=Apply[And,Map[(#<0)&,Part[Transpose@DeleteCases[{ns,np}//Transpose,p_List/;Part[p,1]===0],2]]];


InnerCollectFunction=Factor;


ApartIR/:MakeBoxes[ApartIR[pcs_List,cs_List,np_List,vars_List],TraditionalForm]:=With[{exp=Apply[Times,(Map[(#.vars)&,pcs]+cs)^np]},RowBox[{"\[LeftDoubleBracketingBar]",MakeBoxes[exp,TraditionalForm],"\[RightDoubleBracketingBar]"}]];


ApartIRSort[exp_]:=exp/.ApartIR[pcs_,cs_,np_,vars_]:>ApartIR[Sequence@@PcsCsNpSort[pcs,cs,np],vars];


PcsCsNpSort[pcs_List,cs_List,np_List]:=PcsCsNpSort[pcs,cs,np]=Transpose@Sort[Transpose[{pcs,cs,np}],Less[Part[#1,1],Part[#2,1]]&]


Clear[InnerApart,CachedApart];
ClearCachedApart[]:=Clear[CachedApart];


InnerApart[pcs_List,cs_List,np:{___,0,___},vars_List]:=InnerApart[Sequence@@Transpose@DeleteCases[{pcs,cs,np}//Transpose,p_List/;Part[p,3]===0],vars];


InnerApart[xpcs_List,xcs_List,xnp_List,vars_List]:=Module[{VF,in,tmp,ns,res,p,pcs,cs,np},
{pcs,cs,np}=PcsCsNpSort[xpcs,xcs,xnp];
If[Head[CachedApart[pcs,cs,np]]=!=CachedApart,Return[CachedApart[pcs,cs,np]];];
ns=CachedNullSpace[pcs,cs];
If[ns===False,
tmp=ApartIR[pcs,cs,np,vars];
CachedApart[pcs,cs,np]=tmp;
Return[tmp];
];
(*-------------------------------------------------------------------------------*)
(*Print[ns];*)
(*-------------------------------------------------------------------------------*)
If[CachedNsNp[ns,np],
res=CachedDot[ns,cs];
If[res===0,
p=First[FirstPosition[ns,pa_/;pa=!=0,{1},Heads->False]];
tmp=Table[Block[{lnp=np},If[i==p,0,
If[Part[ns,i]===0,0,Part[lnp,p]--;Part[lnp,i]++;-Part[ns,i]/Part[ns,p] InnerApart[pcs,cs,lnp,vars]]
]],{i,Length[ns]}];
tmp=Collect[Plus@@tmp,_ApartIR,InnerCollectFunction];
CachedApart[pcs,cs,np]=tmp;
Return[tmp];
];
(*Else Part*)
tmp=Table[Block[{lnp=np},
If[Part[ns,i]===0,0,Part[lnp,i]++;Part[ns,i]/res InnerApart[pcs,cs,lnp,vars]]
],{i,Length[ns]}];
tmp=Collect[Plus@@tmp,_ApartIR,InnerCollectFunction];
CachedApart[pcs,cs,np]=tmp;
Return[tmp];
];
(*-------------------------------------------------------------------------------*)
p=First[FirstPosition[np,pa_/;pa>0,{1},Heads->False]];
If[Part[ns,p]===0,
tmp=Block[{lnp=np},Part[lnp,p]=0;InnerApart[pcs,cs,lnp,vars]];
tmp=tmp/.ApartIR[ypcs_,ycs_,ynp_,_]:>InnerApart[Prepend[ypcs,Part[pcs,p]],Prepend[ycs,Part[cs,p]],Prepend[ynp,Part[np,p]],vars];
tmp=Collect[tmp,_ApartIR,InnerCollectFunction];
CachedApart[pcs,cs,np]=tmp;
Return[tmp];
];
(*Else Part*)
res=CachedDot[ns,cs];
tmp=Table[Block[{lnp=np},Part[lnp,p]--;If[i==p,If[res===0,0,res/Part[ns,p] InnerApart[pcs,cs,lnp,vars]],Part[lnp,i]++;
If[Part[ns,i]===0,0,-Part[ns,i]/Part[ns,p] InnerApart[pcs,cs,lnp,vars]]
]],{i,Length[ns]}];
tmp=Collect[Plus@@tmp,_ApartIR,InnerCollectFunction];
CachedApart[pcs,cs,np]=tmp;
Return[tmp];
];


(* ::Subsection::Closed:: *)
(*InnerLog & ApartParse*)


Clear[InnerLog];
InnerLog[x_ y_]:=InnerLog[x]+InnerLog[y];
InnerLog[Power[x_,y_]]:=y InnerLog[x];


Clear[ApartAll];
ApartAll[exp_,vars_List]:=Module[{tmp,VF},
tmp=Cases[InnerLog[exp]/.c_. InnerLog[y_]:>VF[Normal@CoefficientArrays[y,vars],c],_VF,{0,Infinity}];
tmp=tmp/.VF[p_List,np_]:>{Part[p,2],Part[p,1],np};
tmp=Transpose[tmp];
tmp=Append[tmp,vars];
tmp=InnerApart@@tmp;
Return[tmp];
];


(* ::Subsection:: *)
(*Some Auxiliary Function*)


Clear[ApartUnion];
ApartUnion[exp_]:=Cases[exp,_ApartIR,{0,Infinity}]//Union;


Clear[ApartComplete];
ApartComplete[exp_ApartIR]:=Module[{tmp,i,vars},
tmp=exp/.ApartIR->List;
vars=Part[tmp,4];
If[Length[Part[tmp,1]]>=Length[vars],Return[exp]];
For[i=1,i<=Length[vars],i++,
If[MatrixRank[Join[Part[tmp,1],{Part[Normal@CoefficientArrays[Part[vars,i],vars],2]}]]>Length[Part[tmp,1]],
AppendTo[Part[tmp,1],Part[Normal@CoefficientArrays[Part[vars,i],vars],2]];
AppendTo[Part[tmp,2],0];
AppendTo[Part[tmp,3],0];
If[Length[Part[tmp,1]]>=Length[vars],Break[];];
];
];
Return[ApartIR@@tmp];
];


ApartComplete[exp_]:=exp/.a_ApartIR:>ApartComplete[a];


RemoveApart[exp_]:=exp/.ApartIR[pcs_,cs_,np_,vars_]:>Apply[Times,(Map[(#.vars)&,pcs]+cs)^np];


FireArguments[ApartIR[pcs_,cs_,np_,vars_],p2pn_:Identity]:=FireArguments[ApartIR[pcs,cs,np,vars],p2pn]=Sequence[p2pn[Map[(#.vars)&,pcs]+cs],-np];
