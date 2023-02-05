# TensorAlgebra.wl
A Mathematica package to perform tensor algebra, including an advanced tensor expand, and tensor derivative.

```
<< "<DirectoryOfThisPackage>/TensorAlgebra.wl";


(*Define your tensors*)
matrices = {F, \[Delta]F};
symMatrices = {S, \[Delta]S};
skwMatrices = {W, \[Delta]W};
scalars = {a, a[_]};
$Assumptions = (# \[Element] Reals & /@ scalars);
$Assumptions = $Assumptions~Join~MatrixAssumptions[matrices, symMatrices, skwMatrices];
   
?"TensorAlgebra`*"

(* TensorExpand2 distributes tensor multiplication and terms involving Tr and Det . 
   Mathematica provides its own function call TensorExpand which is very limited and in first versions had errors*)
scalar = (Tr[(a[1] S).(a[3] F + a[4] δF) . S . S . F + Transpose[S . S . F] + Transpose[F . S . F]] Tr[a[2] F . S . F] + Det[a S.F.MatrixPower[F, -1]])^2; 
scalarExpand = TensorExpand@TensorExpand2[scalar];

(*To differentiate the scalar (composed  of Tr and Det and Dot) in \
terms of S we use *)
DscalarDS = DTensor[scalar, S, \[Delta]S];
(*Where \[Delta]S is just som dummy Tensor. It should have the same \
properties as S (i.e. symmetric and be assumed to be a Tensor). If \
instead of S you give \[Delta]F the result could be different*)

```
