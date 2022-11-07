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
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ||) l)) in
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


Definition CUE_1 l (updateId :  uint64) (code : optional cell_) : Prop :=
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() || ) l) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  hmapIsMember msgPubkey custodians = true.

Definition CUE_2 l id (updateId :  uint64) (code : optional cell_) (custodianIndex :  uint8) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ||) l) in
  let l' := exec_state (Uinterpreter (_confirmUpdate rec def updateId custodianIndex)) l in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  correctState l ->
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  hmapIsMember msgPubkey custodians = true ->
  REU_1 l' id codeHash owners reqConfirms lifetime.

Definition CUE_3 l id (updateId :  uint64) (code : optional cell_) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
  let l' := exec_state (Uinterpreter (executeUpdate rec def updateId code)) l in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id m_updateRequests) dummyRequest  in
  let tr_id := getPruvendoRecord UpdateRequest_ι_id u in 
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
  correctState l ->
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  hmapIsMember id m_updateRequests = true ->
  REU_1 l' id codeHash owners reqConfirms lifetime ->
  tr_id = id -> 3 * signs >= 2 * (length_ m_custodians)
  .

Definition CUE_6_2 l (updateId :  uint64)  (code : optional cell_) : Prop := 
  let l' := exec_state (Uinterpreter (executeUpdate rec def updateId code)) l in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  let m_updateRequests_old := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let m_lifetime := toValue (eval_state (sRReader (m_lifetime_right rec def) ) l') in
  let m_lifetime_old := toValue (eval_state (sRReader (m_lifetime_right rec def) ) l) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ||) l)) in
  let expiredRequests := xHMapFilter (fun k v =>
    N.leb ((N.shiftr (uint2N k) 32) + uint2N m_lifetime_old) tvm_now
  ) m_updateRequests_old in
  let commonRequests := xHMapFilter (fun k v => 
    andb (hmapIsMember k m_updateRequests_old)
    (Common.eqb v (hmapFindWithDefault dummyRequest k m_updateRequests_old))) m_updateRequests in
  let ur := xMaybeMapDefault (fun x => x) (hmapLookup updateId m_updateRequests_old) dummyRequest  in
  let owners := getPruvendoRecord UpdateRequest_ι_custodians ur in 
  let reqConfirms := getPruvendoRecord UpdateRequest_ι_reqConfirms ur in 
  let lifetime := getPruvendoRecord UpdateRequest_ι_lifetime ur in
  let ecode := (toValue (eval_state (sRReader || tvm->code() ||) l')) in
  let ecode_old := (toValue (eval_state (sRReader || tvm->code() ||) l)) in
  let ccode := (toValue (eval_state (sRReader || tvm->currentCode() ||) l')) in
  let ccode_old := (toValue (eval_state (sRReader || tvm->currentCode() ||) l)) in
  let m_custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l') in
  let m_custodians_old := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let m_ownerKey_old := toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l) in
  let m_ownerKey := toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l') in
  let m_defaultRequiredConfirmations := toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l') in
  let m_defaultRequiredConfirmations_old := toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l) in
  let DEFAULT_LIFETIME := toValue (eval_state (sRReader (DEFAULT_LIFETIME_right rec def) ) l) in
  let m_requestsMask := toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l') in
  let m_updateRequestsMask := toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) l') in
  let m_transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  correctState l ->
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  length_ m_updateRequests_old - length_ expiredRequests - 1 = length_ m_updateRequests /\
  length_ commonRequests = length_ m_updateRequests_old /\
  (xMaybeIsSome code = true -> 
        ccode = xMaybeMapDefault Datatypes.id code default /\
        ecode = xMaybeMapDefault Datatypes.id code default
  ) /\
  (xMaybeIsSome code = false ->
        ccode = ccode_old /\ ecode = ecode_old) /\
  (xMaybeIsSome owners = true -> length_ (xMaybeMapDefault Datatypes.id owners default) >= length_ m_custodians ) /\
  (xMaybeIsSome owners = true -> checkMap1 m_custodians = true) /\
  checkMap2 m_custodians (N.to_nat (length_ (xMaybeMapDefault Datatypes.id owners default))) (xMaybeMapDefault Datatypes.id owners default) = true /\
  (xMaybeIsSome owners = false -> m_custodians = m_custodians_old /\ m_ownerKey = m_ownerKey_old) /\
  (xMaybeIsSome reqConfirms = true -> uint2N m_defaultRequiredConfirmations = N.min (length_ m_custodians) (uint2N (xMaybeMapDefault Datatypes.id reqConfirms default))) /\
  (xMaybeIsSome reqConfirms = false -> m_defaultRequiredConfirmations = m_defaultRequiredConfirmations_old).
  (* BUG in multisig!! *)
  (*(xMaybeIsSome lifetime = false -> m_lifetime = m_lifetime_old) /\
  (xMaybeIsSome lifetime = true -> uint2N (xMaybeMapDefault Datatypes.id lifetime default) > 0 -> m_lifetime = (xMaybeMapDefault Datatypes.id lifetime default)) /\
  (xMaybeIsSome lifetime = true -> uint2N (xMaybeMapDefault Datatypes.id lifetime default) = 0 -> m_lifetime = DEFAULT_LIFETIME) /\ *)
  (* NOT SUPPORTED in multisig! *)
  (*N.land (uint2N m_updateRequestsMask) (0xFFFFFFFF) = 0 /\
  m_transactions = default /\
  m_updateRequests = default /\
  uint2N m_requestsMask = 0. *)