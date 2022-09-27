Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String.
Require Import Setoid. 
Require Import ZArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Ascii.

Require Import FinProof.All.

Require Import UMLang.All. 
Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Require Import UrsusStdLib.Solidity.All.
Require Import UrsusStdLib.Solidity.unitsNotations.
Require Import UrsusTVM.Solidity.All.
Require Export UrsusContractCreator.UrsusDefinitions.
Require Export UrsusContractCreator.ReverseTranslatorConstructions.

Import UrsusNotations.
Local Open Scope xlist_scope.
Local Open Scope record.
Local Open Scope program_scope.
Local Open Scope glist_scope.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.

From elpi Require Import elpi.


Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Require Import multisig2. 

Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Require Import FinProof.CommonInstances.

Require Import CommonQCEnvironment.
Require Import LocalState.
Require Import CommonForProps.

(* 0: constructor
   1: confirmUpdate
   2: submitUpdate
   3: confirmTransaction
   4: submitTransaction
   5: sendTransaction 
   6: executeUpdate
*)

Definition CS_0 l (owners : listArray uint256) (reqConfirms :  uint8) : Prop := 
  let l' := exec_state (Uinterpreter (constructor rec def owners reqConfirms)) l in 
  correctState l' \/ 
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = true.

Definition CS_1 l (updateId :  uint64) : Prop :=
  let l' := exec_state (Uinterpreter (confirmUpdate rec def updateId)) l in 
  correctState l ->
  correctState l'.

Definition CS_2 l (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop :=
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l in 
  correctState l ->
  correctState l'.

Definition CS_3 l (transactionId :  uint64) : Prop :=
  let l' := exec_state (Uinterpreter (confirmTransaction rec def transactionId)) l in 
  correctState l ->
  correctState l'.

Definition CS_4 l (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l in 
  correctState l ->
  correctState l'.

Definition CS_5 l (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint16) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (sendTransaction rec def dest value bounce flags payload)) l in 
  correctState l ->
  correctState l'.

Definition CS_6 l (updateId :  uint64) (code :  TvmCell) : Prop :=
  let l' := exec_state (Uinterpreter (executeUpdate rec def updateId code)) l in 
  correctState l ->
  correctState l'.