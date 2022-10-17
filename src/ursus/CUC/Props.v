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
Require Import SetcodeMultisig. 

Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Require Import FinProof.CommonInstances.

Require Import CommonQCEnvironment.
Require Import SetcodeMultisig_LocalState. 
Require Import CommonForProps.

Definition dummyRequest : UpdateRequestLRecord := Eval compute in default. 

Definition REU_1 l id (codeHash :  option uint256) (owners :  optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
  let m_lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in (* TODO *)
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let l' := exec_state (Uinterpreter (_removeExpiredTransactions rec def)) l in 
  let ret_l := exec_state (Uinterpreter (_removeExpiredUpdateRequests rec def)) l in 
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let m_updateRequests' := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) ret_l) in
  let m_updateRequestsMask := toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) ret_l) in
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l) = false -> 
  hmapIsMember id m_updateRequests = true ->
  N.shiftr 32 (uint2N id) + m_lifetime <= tvm_now <-> 
  hmapIsMember id m_updateRequests' = false /\
  N.shiftl (uint2N id) (uint2N m_updateRequestsMask) = 0.

Definition CUC_1 l (updateId :  uint64) (code : optional cell_) : Prop :=
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey()  ) l) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  hmapIsMember msgPubkey custodians = true.

Definition CUC_2 l id (updateId :  uint64) (code : optional cell_) (custodianIndex :  uint8) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (_confirmUpdate rec def updateId custodianIndex)) l in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let m_lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  tvm_now > m_lifetime ->
  correctState l ->
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  hmapIsMember msgPubkey custodians = true ->
  REU_1 l' id codeHash owners reqConfirms lifetime.

Definition CUC_3 l id (updateId :  uint64) (code : optional cell_) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (executeUpdate rec def updateId code)) l in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id m_updateRequests) dummyRequest  in
  let confirmationsMask := getPruvendoRecord UpdateRequest_ι_confirmationsMask u in 
  let tr_id := getPruvendoRecord UpdateRequest_ι_id u in 
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let m_lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  tvm_now > m_lifetime ->
  correctState l ->
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  hmapIsMember msgPubkey custodians = true ->
  hmapIsMember id m_updateRequests = true ->
  REU_1 l' id codeHash owners reqConfirms lifetime ->
  tr_id = id ->
  N.shiftl (uint2N id) (uint2N confirmationsMask) = 0.  


Definition CUC_4 l id (updateId :  uint64)  (code : optional cell_) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
  let l' := exec_state (Uinterpreter (executeUpdate rec def updateId code)) l in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id m_updateRequests) dummyRequest  in
  let tr_id := getPruvendoRecord UpdateRequest_ι_id u in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let m_lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  tvm_now > m_lifetime ->
  correctState l ->
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  hmapIsMember id m_updateRequests = true ->
  REU_1 l' id codeHash owners reqConfirms lifetime ->
  tr_id = id. 

Definition CUC_5 l id (updateId :  uint64) (custodianIndex :  uint8) (code : optional cell_) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
  let l' := exec_state (Uinterpreter (executeUpdate rec def updateId code)) l in
  let l_res := exec_state (Uinterpreter (_confirmUpdate rec def updateId custodianIndex)) l in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  let m_updateRequests_res := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l_res) in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id m_updateRequests) dummyRequest  in
  let u2 := xMaybeMapDefault (fun x => x) (hmapLookup id m_updateRequests_res) dummyRequest  in
  let confirmationsMask := getPruvendoRecord UpdateRequest_ι_confirmationsMask u in 
  let tr_id := getPruvendoRecord UpdateRequest_ι_id u in 
  let id_u2 := getPruvendoRecord UpdateRequest_ι_id u2 in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let m_lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  tvm_now > m_lifetime ->
  correctState l ->
  hmapIsMember msgPubkey custodians = true ->
  hmapIsMember id m_updateRequests = true ->
  REU_1 l' id codeHash owners reqConfirms lifetime ->
  tr_id = id -> 
  N.shiftl (uint2N id) (uint2N confirmationsMask) = 0 ->
  isError (eval_state (Uinterpreter (_confirmUpdate rec def updateId custodianIndex)) l) = false  /\
  (u2 <> u -> hmapIsMember id_u2 m_updateRequests = true -> hmapIsMember id_u2 m_updateRequests_res = true) /\
  length_ m_updateRequests_res = length_ m_updateRequests.