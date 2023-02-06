(* ::Package:: *)

BeginPackage["TensorAlgebra`"]

ClearAll @@ Names["TensorAlgebra`*"];

DTensor::usage="DTensor[f, T, identity_:MatrixPower[T,0] ] gives the derivative of the scalar f in terms of the tensor T."
Cayley::usage="Cayley[F, identity_:MatrixPower[Id,0] ] gives the expanded Cayley Hamilton theorem, which should equal zero."
InverseFromCayley::usage="InverseFromCayley[F] returns a the inverse of F in terms of powers 0,1,2 of F by using Cayley[F]."
Characteristic::usage="Characteristic[F,\[Lambda]] gives the expanded characteristic of F, which should equal zero."
subDetExpand::usage=" Distributes Det[A_+B_] ."
TensorProductExpand::usage="TensorProductExpand[tensor] will expand a tensor such as TensorContract[T\[TensorProduct]A\[TensorProduct]\!\(\*
StyleBox[\"B\",\nFontWeight->\"Bold\"]\),list] and reduce, much like the in-built TensorExpand in version 10.1\!\(\*
StyleBox[\"  \",\nFontWeight->\"Bold\"]\)"
TensorExpand2::usage="TensorExpand2[tensor,AssumeNotTensor_:True] will expand and reduce tensor expressions that involve Tr, Det and Dot. As a default it assumes that any smybol that has not been defined as a tensor is a scalar and will be treated as such.  "
subDisplay::usage="Substitutes everything in a MatrixPower or Tr into a string which is easier to read."
MatrixAssumptions::usage="MatrixAssumptions[matrices_,symmatrices_:{},skwmatrices_:{}] takes each element of matrices and returns the assumptions that it and it's MatrixPowers are a 3x3 matrix. Likewise for symmatrices and skwmatrices. "
subUncontractTensor::usage="T/.subUncontractTensor[\[Delta]C_,identity_:Id] will remove the tensor \[Delta]C and return a matrix M such that M:\[Delta]C == T. "
subMatrixPowerToDot::usage "T/.subMatrixPowerToDot will change all MatrixPowers to Dot"
ExtractTensorFirstOrder\[Delta]::usage="If tensor is a sum of terms with tensors and trace, then ExtractTensorFirstOrder\[Delta][tensor,\[Delta]] will return only the terms which have a linear contribution from \[Delta]"

Begin["`Private`"]

subMatrixPowerToDot = MatrixPower[A_,n_]:> Dot@@Table[A,n]/;(n>0 &&n\[Element]Integers);

subDisplay ={ 
   Transpose[MatrixPower[A_,-1],{2,1}]:> 


\!\(\*SuperscriptBox[\(ToString[A\ ]\), \("\<-T\>"\)]\),
   Transpose[MatrixPower[A_,-1]]:>


\!\(\*SuperscriptBox[\(ToString[A]\), \("\<-T\>"\)]\),
   Transpose[A_]:> 


\!\(\*SuperscriptBox[\(A\), \("\<T\>"\)]\),
   Transpose[A_,{2,1}]:>

\!\(\*SuperscriptBox[\(ToString[A]\), \("\<T\>"\)]\),
   MatrixPower[_ ,0]->"I",MatrixPower[A_,n_]:>A^ToString[n] ,
a_[n_]:> Subscript[a, n]/;IntegerQ[n]
};

MatrixAssumptions[matrices_,symmatrices_:{},skwmatrices_:{}]:=Module[{assumptions={}},
   assumptions=assumptions \[Union]Flatten[{#\[Element]Matrices[{3,3},Reals],MatrixPower[#,-1]\[Element]Matrices[{3,3},Reals ],Inverse[#]\[Element]Matrices[{3,3},Reals ]}&/@matrices];
   assumptions=assumptions \[Union]Flatten[{#\[Element]Matrices[{3,3},Reals,Symmetric[{1,2}]], MatrixPower[#,-1]\[Element]Matrices[{3,3},Reals,Symmetric[{1,2}] ],Inverse[#]\[Element]Matrices[{3,3},Reals,Symmetric[{1,2}] ]}&/@symmatrices];
   assumptions=assumptions \[Union]Flatten[{#\[Element]Matrices[{3,3},Reals,Antisymmetric[{1,2}]], MatrixPower[#,-1]\[Element]Matrices[{3,3},Reals,Antisymmetric[{1,2}] ],Inverse[#]\[Element]Matrices[{3,3},Reals,Antisymmetric[{1,2}] ]}&/@skwmatrices];
  Return@assumptions
];

Cayley[F_,identity_:MatrixPower[Global`Id,0]]:= Distribute[F . F . F]-Distribute[Tr[F]]Distribute[F . F] +F (Distribute[Tr[F]]^2-Distribute[Tr[F . F //Distribute]])/2  - Det[F]identity ;
Characteristic[F_,\[Lambda]_]:= \[Lambda]^3-Distribute[Tr[F]]\[Lambda]^2 +\[Lambda] (Distribute[Tr[F]]^2-Distribute[Tr[F . F //Distribute]])/2  - Det[F] ;

InverseFromCayley[F_]:=
(Cayley[F] . MatrixPower[F,-1]/Det[F] +MatrixPower[F,-1] //TensorExpand) ;

subDetExpand= {Det[A_+B_]:>( Det[A] +  Det[A] Distribute@Tr[InverseFromCayley[A] . B//TensorExpand ] +  Det[B]Distribute@Tr[InverseFromCayley[B] . A//TensorExpand] + Det[B]  //TensorExpand)/.subMatrixPowerToDot};

(*subTensorProductExpand= { TensorContract[n_\[TensorProduct]TensorContract[m_,list1_]\[TensorProduct]p_,list2_] :> TensorContract[n\[TensorProduct]m\[TensorProduct]p,
          Sort[Join[ list1+TensorRank[n],Map[Complement[ Range[TensorRank[n\[TensorProduct]m\[TensorProduct]p]],Flatten[list1+TensorRank[n]] ][[#]] &,list2]]]
 ] 
};*)

subTensorProductExpand= { TensorContract[Dot[n_,TensorContract[m_,list1_],p_],list2_] :> TensorContract[Dot[n,m,p],
          Sort[Join[ list1+TensorRank[n],Map[Complement[ Range[TensorRank[Dot[n,m,p]]],Flatten[list1+TensorRank[n]] ][[#]] &,list2]]]
 ] 
};

subTensorProductExpand =subTensorProductExpand~Join~{TensorContract[m_Plus,list_]:>(TensorContract[#,list]&/@m )};

subTensorDistribute= {Dot[n__,m_Plus]:>Plus@@((Dot[n,#])&/@(List@@m)),Dot[n_Plus,m__]:>Plus@@(Dot[#,m]&/@(List@@n))};
subTensorDistribute=subTensorDistribute~Join~{
Dot[n__,m_Times]:> (listm=List@@m; pos= Position[TensorRank/@listm,_Integer]; If[(Length@pos)!=1, Message[TensorExpand2::argerror,"TensorDistribute::found Times[Tensor,Tensor]"]]; pos=First@pos ; (Dot[n,First[Take[listm,pos]]])  Times@@ Drop[listm,pos ]  ),
Dot[n_Times,m__]:> (listm=List@@n; pos= Position[TensorRank/@listm,_Integer]; If[(Length@pos)!=1, Message[TensorExpand2::argerror,"found Times[Tensor,Tensor]"]];pos=First@pos ; (Dot[First[Take[listm,pos]],m])  Times@@ Drop[listm,pos ]  ),

TensorContract[ n_Times,list_]:> (listm=List@@n;pos= Position[TensorRank/@listm,_Integer]; If[(Length@pos)!=1, Print["Errors found Times[Tensor,Tensor]"]];pos=First@pos ; (TensorContract[  First[Take[listm,pos]],list])  Times@@ Drop[listm,pos ]  )    };
subUncontractTensor[\[Delta]C_,identity_:Id]:={
   Tr[\[Delta]C]-> MatrixPower[identity,0],
   Tr[Dot[\[Delta]C,n__]]:> Transpose[Dot[n]],
   Tr[Dot[n__,\[Delta]C]]:> Transpose[Dot[n]],
   Tr[Dot[n__,\[Delta]C,m__]]:> Dot[Transpose[Dot[n]],Transpose[Dot[m]]]}~Join~
  {Tr[Transpose[\[Delta]C,{2,1}]]:> MatrixPower[identity,0],
   Tr[Dot[Transpose[\[Delta]C,{2,1}],n__]]:> Dot[n],
   Tr[Dot[n__,Transpose[\[Delta]C,{2,1}]]]:>Dot[n],
   Tr[Dot[n__,Transpose[\[Delta]C,{2,1}],m__]]:> Dot[m,n]};

subTensorProductExpand = subTensorDistribute~Join~subTensorProductExpand;

TensorProductExpand[tensor_]:=tensor//.subTensorProductExpand

subTensorExpand ={
  Tr[Times[a_, b__]]:>a Tr[Times[b]]/;NotTensorQ[a],
  Tr[Times[b__,a_]]:>a Tr[Times[b]]/;NotTensorQ[a],
  Tr[Times[a_, b__]]:>a Tr[Times[b]]/;NotTensorQ[a],
  Tr[Times[b__,a_]]:>a Tr[Times[b]]/;NotTensorQ[a],
  Tr[MatrixPower[A_,0]]:>TensorDimensions[A][[1]]/;TrueQ[TensorRank[A]>0],
  Det[Times[a_ ,A__]]:>  a^3 Det[Times[A]]/;NotTensorQ[a],
  Det[Times[A__,a_]] :>  a^3 Det[Times[A]]/;NotTensorQ[a],
  Det[MatrixPower[A_,n_]]/;Negative[n]:> 1/Det[MatrixPower[A,-n]],
  Det[MatrixPower[A_,n_]]:> Det[A]^n,
  Tr[n_]:> Plus@@(Tr/@(List@@n))/;(Head[n]==Plus)  
};
subReduceTr={
   Tr[0]->0, 
   Tr[Transpose[A__,{2,1}]]:> Tr[A],
   Tr[Dot[MatrixPower[a_,-1],a_]]-> 3,
   Tr[Dot[a_,MatrixPower[a_,-1]]]-> 3,
   Tr[Dot[a_,b__,MatrixPower[a_,-1]]]:>  Tr[Dot[b]],
   Tr[Dot[MatrixPower[a_,-1],b__,a_]]:>  Tr[Dot[b]],
   Tr[Dot[MatrixPower[a_,n_],b__,MatrixPower[a_,m_] ]]->Tr[Dot[MatrixPower[a,n+m],b]],
   Tr[Dot[MatrixPower[a_,n_],b__,a_ ]]:>Tr[Dot[MatrixPower[a,n+1],b]],
   Tr[Dot[a_,b__,MatrixPower[a_,m_] ]]:>Tr[Dot[MatrixPower[a,1+m],b]],
   Tr[Dot[a_,b__,a_]]:>Tr[Dot[MatrixPower[a,2],b]],
   Tr[Dot[MatrixPower[a_,n_],b__,MatrixPower[c_,m_] ]]:> Tr[Dot[MatrixPower[c,m],MatrixPower[a,n],b]]/;m>n,
   Tr[Dot[MatrixPower[a_,n_],MatrixPower[c_,m_] ]]:> Tr[Dot[MatrixPower[c,m],MatrixPower[a,n]]]/;m>n,
   Tr[Dot[a_,b__,MatrixPower[c_,m_] ]]:> Tr[Dot[MatrixPower[c,m],a,b]]/;(Head[a]=!=MatrixPower && (Head[a]!= MatrixPower)),
   Tr[Dot[a_,MatrixPower[c_,m_] ]]:> Tr[Dot[MatrixPower[c,m],a]]/;(Head[a]=!=MatrixPower &&(Head[a]!= MatrixPower))
 };
(*subTensorExpand=subTensorExpand~Join~subDetExpand~Join~subReduceTr;*)
subTensorExpand=subTensorExpand~Join~subReduceTr;

(*Below Expands a (__).(__), where as TensorExpand might just give a MatrixPower of the whole thing*)
subExpandMatrixPower=Module[{B,C,A},
  {
   Dot[Times[a_,B__],A__]:> Times[a,Dot[Times[B],A]]/;NotTensorQ[a],
   Dot[A__,Times[a_,B__]]:> Times[a,Dot[A,Times[B]]]/;NotTensorQ[a],
   Dot[a_,b_]:>  Distribute[Dot[a,b]]/;(Head[a]==Plus||Head[b]==Plus),
   Dot[A__,a__]:>Times[a,Dot[A]]/;NotTensorQ[a],
   Dot[a__,A__]:> Times[a,Dot[A]]/;NotTensorQ[a],
   Dot[CC__,a_,A__]:> Times[Tr[B],Dot[CC,A]]/;NotTensorQ[a],
   Tr[Dot[MatrixPower[_,0],a_]]:> Times[3,a]/;NotTensorQ[a],
   Dot[MatrixPower[_,0],A__]:> Dot[A]/;TrueQ[TensorRank[Dot[A]]>0],
   Dot[A__,MatrixPower[_,0]]:> Dot[A]/;TrueQ[TensorRank[Dot[A]]>0]
  }
];
subTensorExpand=subTensorExpand~Join~subExpandMatrixPower;

TensorExpand2::argerror = "Argument given to TensorDistribute: `1`";
TensorExpand2[tensor_,AssumeNotTensor_:True]:=(
NotTensorQ[A_]:=If[AssumeNotTensor, 
	UnsameQ[!Positive@TensorRank@A,False], 
	SameQ[!Positive@TensorRank@A,True] ,UnsameQ[!Positive@TensorRank@A,False]
];
  (*TensorExpand[tensor//.subTensorExpand]*)
 tensor//.subTensorExpand
);

subExpandDetTensor[term_,\[Delta]_] := term/.{Det[Plus[n__]+ \[Delta]]:>Det[Plus[n]] +Det[Plus[n]]Tr[MatrixPower[Plus[n],-1] . \[Delta]]};

subExpandInverseTensor[term_,\[Delta]_] := term/.{MatrixPower[Plus[n__]+ \[Delta],-1]:>MatrixPower[Plus[n],-1] - MatrixPower[Plus[n],-1] . \[Delta] . MatrixPower[Plus[n],-1]};

(*This function returns the derivative of the tensor in relation to \[Delta].*)
ExpandTensor\[Delta][tensor_,\[Delta]_] := Module[{Expandedtensor = tensor},
	Expandedtensor=(Expandedtensor/.subMatrixPowerToDot//TensorProductExpand//TensorExpand2//TensorExpand//Expand)/.subMatrixPowerToDot;

	(*Expand any determinant*)
	Expandedtensor = subExpandDetTensor[Expandedtensor,\[Delta]];

	(*Expand any inverse matrix*)
	Expandedtensor = subExpandInverseTensor[Expandedtensor,\[Delta]];

	Return@ Flatten[{List@@Expand[Expandedtensor]}]
]
ExtractTensorFirstOrder\[Delta][tensor_,\[Delta]_] := Plus@@Reap[
	If[ Count[{#},\[Delta],\[Infinity],Heads-> True]=== 1 && Count[Cases[{#},Tr[n_]^m_:> n/;m!=1,\[Infinity],Heads-> True],\[Delta],\[Infinity]]===0,
	Sow[#],Sow[0]
	]&/@ExpandTensor\[Delta][tensor,\[Delta]]
][[2,1]];

DTensor[f_,T_,\[Delta]_,Id_:Global`Id]:= Module[{result}, 
result = Expand@TensorExpand@TensorExpand2[f]/.subMatrixPowerToDot;
result = ExtractTensorFirstOrder\[Delta][result/.{T->T+\[Delta]},\[Delta]];
result = result/.subUncontractTensor[\[Delta],Id]//TensorExpand2//TensorExpand;

Return[result/.subMatrixPowerToDot]
];


End[];
EndPackage[];









