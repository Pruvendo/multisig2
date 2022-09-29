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

Definition STS_1 l (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint8) (payload :  cell_) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  correctState l ->
  isError (eval_state (Uinterpreter (sendTransaction rec def dest value bounce flags payload)) l) = false ->
  length_ custodians = 1.

Definition STS_2 l (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint8) (payload :  cell_) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  correctState l ->
  isError (eval_state (Uinterpreter (sendTransaction rec def dest value bounce flags payload)) l) = false ->
  hmapIsMember msgPubkey custodians = true.

Definition STS_3_1 l (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint8) (payload :  cell_) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  correctState l ->
  length_ custodians = 1 ->
  hmapIsMember msgPubkey custodians = true ->
  isError (eval_state (Uinterpreter (sendTransaction rec def dest value bounce flags payload)) l) = false.

Definition equalExceptMessagesLocalBalanceAccepted (l l': LedgerLRecord rec) := 
  ledgerEqb {$$ {$$ {$$ l with Ledger_VMState := 
  {$$ {$$
   getPruvendoRecord Ledger_VMState l
   with VMState_ι_accepted := true $$} : @field_type (LedgerLRecord rec) _ _ Ledger_VMState with 
   VMState_ι_balance := getPruvendoRecord VMState_ι_balance 
     (getPruvendoRecord Ledger_VMState l')
   
 $$} 
$$} with Ledger_LocalState := getPruvendoRecord Ledger_LocalState l' 
$$} with Ledger_MessagesState := getPruvendoRecord Ledger_MessagesState l' 
$$} l'.
(* TODO *)
(* Definition STS_3_2 (l: LedgerLRecord rec) (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint16) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (sendTransaction rec def dest value bounce flags payload)) l in 
  let FLAG_IGNORE_ERRORS := uint2N (toValue (eval_state (sRReader (FLAG_IGNORE_ERRORS_right rec def) ) l)) in
  let flags' := Build_XUBInteger (N.lor (uint2N flags) FLAG_IGNORE_ERRORS) in
  let mes := (EmptyMessage IDefault (value, (bounce, (flags', payload)))) in
  let messageQueueDefault := (toValue (eval_state (sRReader (ULtoRValue ( IDefault_left rec def ))) l')) in
  let messageQueueTmp := (toValue (eval_state (sRReader (ULtoRValue ( Itmp_left rec def ))) l'))  in 
  correctState l ->
  isError (eval_state (Uinterpreter (sendTransaction rec def dest value bounce flags payload)) l) = false ->
  isOnlyMessage messageQueueDefault = true /\
  length_ messageQueueTmp = 0 /\
  isMessageSent mes dest 0 messageQueueDefault = true /\
  equalExceptMessagesLocalBalanceAccepted l l' = true.
 *)  (* NYI: msg.params.payload = params.payload *)