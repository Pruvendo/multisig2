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


Definition dummyTransaction : TransactionLRecord := Eval compute in default. 

Definition REU_1 l id (codeHash :  option uint256) (owners :  optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional  ( uint64 )) : Prop := 
  let m_lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let l' := exec_state (Uinterpreter (_removeExpiredTransactions rec def)) l in 
  let ret_l := exec_state (Uinterpreter (_removeExpiredUpdateRequests rec def)) l in 
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let m_updateRequests' := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) ret_l) in
  let m_updateRequestsMask := toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) ret_l) in
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l) = false -> 
  hmapIsMember id m_updateRequests = true ->
  N.shiftr 32 (uint2N id) + m_lifetime <= tvm_now <-> 
  hmapIsMember id m_updateRequests = true /\
  hmapIsMember id m_updateRequests' = false /\
  N.shiftl (uint2N id) (uint2N m_updateRequestsMask) = 0.

Definition CUR_1 l (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional  ( uint64 )) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l) = false ->
  hmapIsMember msgPubkey custodians = true.

Definition CUR_2 l (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional  ( uint64 )) : Prop := 
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l) = false ->
  xMaybeIsSome codeHash = true ->
  xMaybeIsSome owners = true /\
  length_ (xMaybeMapDefault Datatypes.id owners default) > 0.

Definition CUR_3 l (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional  ( uint64 )) : Prop := 
  let MAX_CUSTODIAN_COUNT := uint2N (toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l)) in
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l) = false ->
  xMaybeIsSome codeHash = true ->
  xMaybeIsSome owners = true /\
  length_ (xMaybeMapDefault Datatypes.id owners default) <= MAX_CUSTODIAN_COUNT. 

Definition CUR_4 id l (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional  ( uint64 )) : Prop := 
  let MAX_CUSTODIAN_COUNT := uint2N (toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l)) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let m_lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  tvm_now > m_lifetime ->
  correctState l ->
  xMaybeIsSome codeHash = true ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l) = false ->
  hmapIsMember msgPubkey custodians = true ->
  xMaybeIsSome owners = true ->
  length_ (xMaybeMapDefault Datatypes.id owners default) > 0 ->
  length_ (xMaybeMapDefault Datatypes.id owners default) <= MAX_CUSTODIAN_COUNT ->
  hmapIsMember id transactions = true ->
  REU_1 l' id codeHash owners reqConfirms lifetime.

Definition CUR_5 l id (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional  ( uint64 )) : Prop := 
  let MAX_CUSTODIAN_COUNT := uint2N (toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l)) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l in
  let m_updateRequestsMask := (uint2N (toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) l'))) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let m_lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  tvm_now > m_lifetime ->
  correctState l -> 
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l) = false ->
  hmapIsMember msgPubkey custodians = true ->
  xMaybeIsSome owners = true ->
  length_ (xMaybeMapDefault Datatypes.id owners default) > 0 ->
  length_ (xMaybeMapDefault Datatypes.id owners default) <= MAX_CUSTODIAN_COUNT ->
  hmapIsMember id transactions = true ->
  REU_1 l' id codeHash owners reqConfirms lifetime ->
  N.land m_updateRequestsMask (uint2N id) = 0.

(* CUR_6_1 checked as part of correctState *)

Definition CUR_6_2 l (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional  ( uint64 )) : Prop :=
  let MAX_CUSTODIAN_COUNT := uint2N (toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l)) in 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  correctState l -> 
  hmapIsMember msgPubkey custodians = true ->
  (xMaybeIsSome owners = true ->
    length_ (xMaybeMapDefault Datatypes.id owners default) > 0 /\
    length_ (xMaybeMapDefault Datatypes.id owners default) <= MAX_CUSTODIAN_COUNT
  ) ->
  (xMaybeIsSome owners = false ->
   xMaybeIsSome codeHash = false) ->
  (*that.m_updateRequestsMask[i] = false*)
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l) = false
  .

Definition dummyRequest : UpdateRequestLRecord := Eval compute in default. 

Definition CUR_6_3 l (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional  ( uint64 )) : Prop :=
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  let requests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let requests' := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  let lifetime_old := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let newRequests := xHMapFilter (fun k v =>
    negb (hmapIsMember k requests)
  ) requests' in
  let expiredRequests := xHMapFilter (fun k v =>
    N.leb ((N.shiftr (uint2N k) 32) + lifetime_old) tvm_now
  ) requests in
  let commonRequests := xHMapFilter (fun k v => 
    andb (hmapIsMember k requests)
    (Common.eqb v (hmapFindWithDefault dummyRequest k requests
  ))) requests' in
  let request := snd (hd (Build_XUBInteger 0, dummyRequest) (unwrap newRequests)) in
  let index := getPruvendoRecord UpdateRequest_ι_index request in
  let signs := getPruvendoRecord UpdateRequest_ι_signs request in
  let creator := getPruvendoRecord UpdateRequest_ι_creator request in
  let codeHash' := getPruvendoRecord UpdateRequest_ι_codeHash request in
  let owners' := getPruvendoRecord UpdateRequest_ι_custodians request in
  let reqConfirms' := getPruvendoRecord UpdateRequest_ι_reqConfirms request in
  let lifetime' := getPruvendoRecord UpdateRequest_ι_lifetime request in
  let mask := getPruvendoRecord UpdateRequest_ι_confirmationsMask request in
  let updateRequestMask := uint2N (toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) l')) in
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l) = false ->
  lifetime_old < tvm_now ->
  length_ newRequests = 1 /\
  uint2N index = i /\
  uint2N signs = 1 /\
  creator = msgPubkey /\
  codeHash' = codeHash /\ owners' = owners /\ 
  reqConfirms' = reqConfirms /\ lifetime' = lifetime /\
  uint2N mask = N.shiftl 1 i /\
  N.land (N.shiftr updateRequestMask i) 1 = 1 /\
  length_ requests' = length_ requests + 1 - length_ expiredRequests /\
  length_ commonRequests = length_ requests - length_ expiredRequests.

Definition CUR_7 l id (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional  ( uint64 )) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l in 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms lifetime)) l) = true ->
  hmapIsMember id transactions = true ->
  REU_1 l' id codeHash owners reqConfirms lifetime \/
  ledgerEqb l l' = true.
