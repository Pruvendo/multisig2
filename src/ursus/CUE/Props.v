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


Definition CUE_1 l (updateId :  uint64) (code : optional cell_) : Prop :=
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey()  ) l) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  hmapIsMember msgPubkey custodians = true.

Definition CUE_2 l id (updateId :  uint64) (code : optional cell_) (custodianIndex :  uint8) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
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

Definition CUE_3 l id (updateId :  uint64) (code : optional cell_) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
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


Definition CUE_4 l id (updateId :  uint64)  (code : optional cell_) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
  let l' := exec_state (Uinterpreter (executeUpdate rec def updateId code)) l in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  let m_custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id m_updateRequests) dummyRequest  in
  let tr_id := getPruvendoRecord UpdateRequest_ι_id u in 
  let signs := uint2N (getPruvendoRecord UpdateRequest_ι_signs u) in 
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let m_lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  tvm_now > m_lifetime ->
  correctState l ->
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  hmapIsMember id m_updateRequests = true ->
  REU_1 l' id codeHash owners reqConfirms lifetime ->
  tr_id = id -> 3 * signs >= 2 * (length_ m_custodians)
  .

Definition CUE_6_2 l id id2 (updateId :  uint64)  (code : optional cell_) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
  let l' := exec_state (Uinterpreter (executeUpdate rec def updateId code)) l in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let res := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  let ur := xMaybeMapDefault (fun x => x) (hmapLookup id m_updateRequests) dummyRequest  in
  let u2 := xMaybeMapDefault (fun x => x) (hmapLookup id2 res) dummyRequest  in
  let tr_id := getPruvendoRecord UpdateRequest_ι_id ur in 
  let tr_id2 := getPruvendoRecord UpdateRequest_ι_id u2 in 
  let pcode := (toValue (eval_state (sRReader || tvm->code() ) l)) in
  let ecode := (toValue (eval_state (sRReader || tvm->code() ) l')) in
  let ccode := (toValue (eval_state (sRReader || tvm->currentCode() ) l')) in
  let m_custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l') in
  let m_custodians_old := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  correctState l ->
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  REU_1 l' id codeHash owners reqConfirms lifetime ->
  (* (u2 <> ur -> hmapIsMember id2 m_updateRequests -> hmapIsMember id2 res) -> *)
  length_ m_updateRequests - 1 = length_ res /\
  tr_id <> tr_id2 /\
  pcode = ecode /\
  ccode = ecode /\
  (xMaybeIsSome owners = true -> length_ (xMaybeMapDefault Datatypes.id owners default) <= length_ m_custodians ) /\
  checkMap1 m_custodians = true /\
  checkMap2 m_custodians (N.to_nat (length_ (xMaybeMapDefault Datatypes.id owners default))) (xMaybeMapDefault Datatypes.id owners default) = true /\
  (xMaybeIsSome owners = false -> m_custodians = m_custodians_old)
  .