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
Require Import UrsusTVM.Solidity.UrsusDefinitions.
Require Import UrsusTVM.Solidity.ReverseTranslatorConstructions.

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
Require Import multisig. 

Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Require Import FinProof.CommonInstances.

Require Import CommonQCEnvironment.
Require Import LocalState.
Require Import CommonForProps.


Definition dummyTransaction : MultisigWallet_ι_TransactionLRecord := Eval compute in default. 

Definition REU_1 l id (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop := 
  let EXPIRATION_TIME := uint2N (toValue (eval_state (sRReader (EXPIRATION_TIME_right rec def) ) l)) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let l' := exec_state (Uinterpreter (_removeExpiredTransactions rec def)) l in 
  let ret_l := exec_state (Uinterpreter (_removeExpiredUpdateRequests rec def)) l in 
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let m_updateRequests' := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) ret_l) in
  let m_updateRequestsMask := toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) ret_l) in
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l) = false -> 
  hmapIsMember id m_updateRequests = true ->
  N.shiftr 32 (uint2N id) + EXPIRATION_TIME <= tvm_now <-> 
  hmapIsMember id m_updateRequests' = false /\
  N.shiftl (uint2N id) (uint2N m_updateRequestsMask) = 0
  .

Definition CUR_1 l (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l) = false ->
  hmapIsMember msgPubkey custodians = true.

Definition CUR_2 l (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop := 
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l) = false ->
  length_ owners > 0 .

Definition CUR_3 l (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop := 
  let MAX_CUSTODIAN_COUNT := uint2N (toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l)) in
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l) = false ->
  length_ owners <= MAX_CUSTODIAN_COUNT . 

Definition CUR_4 id l (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop := 
  let MAX_CUSTODIAN_COUNT := uint2N (toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l)) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l) = false ->
  hmapIsMember msgPubkey custodians = true ->
  length_ owners > 0 ->
  length_ owners <= MAX_CUSTODIAN_COUNT ->
  hmapIsMember id transactions = true ->
  REU_1 l' id codeHash owners reqConfirms.

Definition CUR_5 l id (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop := 
  let MAX_CUSTODIAN_COUNT := uint2N (toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l)) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l in
  let m_updateRequestsMask := (uint2N (toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) l'))) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l) = false ->
  hmapIsMember msgPubkey custodians = true ->
  length_ owners > 0 ->
  length_ owners <= MAX_CUSTODIAN_COUNT ->
  hmapIsMember id transactions = true ->
  REU_1 l' id codeHash owners reqConfirms ->
  N.land m_updateRequestsMask (uint2N id) = 0.


Definition CUR_7 l id (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l in 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l) = true ->
  hmapIsMember id transactions = true ->
  REU_1 l' id codeHash owners reqConfirms. 

Definition CUR_6_1_common l l' req1 req2 req3 req4: Prop := 
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let m_updateRequests_2 := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  let k1 := getPruvendoRecord MultisigWallet_ι_UpdateRequest_ι_id req1 in 
  let k2 := getPruvendoRecord MultisigWallet_ι_UpdateRequest_ι_id req2 in 
  let k3 := getPruvendoRecord MultisigWallet_ι_UpdateRequest_ι_id req3 in 
  let k4 := getPruvendoRecord MultisigWallet_ι_UpdateRequest_ι_id req4 in 
  req1 <> req2 ->
  k1 <> k2 -> 
  hmapIsMember k1 m_updateRequests = true ->
  hmapIsMember k2 m_updateRequests_2 = true -> 
  req3 <> req4 ->
  k3 <> k4 -> 
  hmapIsMember k3 m_updateRequests = true ->
  hmapIsMember k4 m_updateRequests_2 = true.

Definition CUR_6_1_1 l req1 req2 req3 req4 (updateId :  uint64) : Prop :=
  let l' := exec_state (Uinterpreter (confirmUpdate rec def updateId)) l in 
  correctState l ->
  CUR_6_1_common l l' req1 req2 req3 req4.

Definition CUR_6_1_2 l req1 req2 req3 req4 (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop :=
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l in 
  correctState l ->
  CUR_6_1_common l l' req1 req2 req3 req4.

Definition CUR_6_1_3 l req1 req2 req3 req4 (transactionId :  uint64) : Prop :=
  let l' := exec_state (Uinterpreter (confirmTransaction rec def transactionId)) l in 
  correctState l ->
  CUR_6_1_common l l' req1 req2 req3 req4.

Definition CUR_6_1_4 l req1 req2 req3 req4 (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l in 
  correctState l ->
  CUR_6_1_common l l' req1 req2 req3 req4.

Definition CUR_6_1_5 l req1 req2 req3 req4 (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint16) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (sendTransaction rec def dest value bounce flags payload)) l in 
  correctState l ->
  CUR_6_1_common l l' req1 req2 req3 req4.

