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

Definition dummyTransaction : TransactionLRecord := Eval compute in default. 

Definition ETR_1 l u (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) (stateInit :  optional  ( TvmCell )) : Prop := 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  let MAX_CLEANUP_TXNS := uint2N (toValue (eval_state (sRReader (MAX_CLEANUP_TXNS_right rec def) ) l)) in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let id := (getPruvendoRecord Transaction_ι_id u) in
  let l' := exec_state (Uinterpreter (_removeExpiredTransactions rec def)) l in 
  let m_transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l) = false -> 
  hmapIsMember id m_updateRequests = true ->
  (N.shiftr (uint2N id) 32) + lifetime <= tvm_now  ->
  length_ (xHMapFilter (fun _k t => (eqb (getPruvendoRecord Transaction_ι_id t) id)) transactions) < MAX_CLEANUP_TXNS  <->
  hmapIsMember id transactions = true /\
  hmapIsMember id m_transactions = false.


Definition MTS_1 l (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) (stateInit :  optional  ( TvmCell )) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l) = false ->
  hmapIsMember msgPubkey custodians = true.

Definition MTS_2 l id (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) (stateInit :  optional  ( TvmCell )) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l in 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l) = true ->
  hmapIsMember msgPubkey custodians = true ->
  hmapIsMember id transactions = true -> 
  ETR_1 l' u dest value bounce allBalance payload stateInit. 

Definition MTS_3 l (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) (stateInit :  optional  ( TvmCell )) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let requestsMask := toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l) in 
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  let bitsMask := N.land (N.shiftr (uint2N requestsMask) (8 * i)) 255 in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let expiredTransactions := xHMapFilter (fun k v =>
    let index := uint2N (getPruvendoRecord Transaction_ι_index v) in
    andb (N.eqb index i) (N.leb ((N.shiftr (uint2N k) 32) + lifetime) tvm_now)
  ) transactions in
  let bitsMask' := bitsMask - length_ expiredTransactions in
  correctState l ->
  tvm_now > lifetime ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l) = false ->
  bitsMask' < 5. 

Definition MTS_4 l id (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) (stateInit :  optional  ( TvmCell )) : Prop := 
  let FLAG_IGNORE_ERRORS := uint2N (toValue (eval_state (sRReader (FLAG_IGNORE_ERRORS_right rec def) ) l)) in
  let FLAG_SEND_ALL_REMAINING := uint2N (toValue (eval_state (sRReader (FLAG_SEND_ALL_REMAINING_right rec def) ) l)) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let requestsMask := uint2N (toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l)) in (* TODO ? *)
  let m_defaultRequiredConfirmations :=  uint2N (toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l)) in (* ???? *)
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l in
  let messqueue := toValue ((eval_state (sRReader (ULtoRValue (IDefault_left rec def)))) l') in 
  let mes := EmptyMessage IDefault (Build_XUBInteger 0, (bounce, (Build_XUBInteger (N.lor FLAG_IGNORE_ERRORS FLAG_SEND_ALL_REMAINING) , payload))) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l) = false ->
  hmapIsMember msgPubkey custodians = true -> 
  ETR_1 l' u dest value bounce allBalance payload stateInit -> 
  requestsMask < 5 -> 
  m_defaultRequiredConfirmations < 2 ->
  allBalance = true ->
  isOnlyMessage messqueue = true /\
  isMessageSent mes dest 0 messqueue = true . 


Definition MTS_5 l id (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) (stateInit :  optional  ( TvmCell )) : Prop := 
  let FLAG_IGNORE_ERRORS := uint2N (toValue (eval_state (sRReader (FLAG_IGNORE_ERRORS_right rec def) ) l)) in
  let FLAG_PAY_FWD_FEE_FROM_BALANCE := uint2N (toValue (eval_state (sRReader (FLAG_PAY_FWD_FEE_FROM_BALANCE_right rec def) ) l)) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let requestsMask := uint2N (toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l)) in (* ???? *)
  let m_defaultRequiredConfirmations :=  uint2N (toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l)) in (* ???? *)
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l in
  let messqueue := toValue ((eval_state (sRReader (ULtoRValue (IDefault_left rec def)))) l') in 
  let mes := EmptyMessage IDefault (value, (bounce, ((Build_XUBInteger  (N.lor FLAG_IGNORE_ERRORS FLAG_PAY_FWD_FEE_FROM_BALANCE)), payload))) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l) = false ->
  hmapIsMember msgPubkey custodians = true -> 
  ETR_1 l' u dest value bounce allBalance payload stateInit -> 
  requestsMask < 5 -> 
  m_defaultRequiredConfirmations < 2 ->
  allBalance = false ->
  isOnlyMessage messqueue = true /\
  isMessageSent mes dest 0 messqueue = true . 

(* MTS_6_1 checked as part of correctState *)
(* MTS_6_2 checked as part of correctState *)
(* TODO: MTS_6_3 *)

Definition MTS_7 l id (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) (stateInit :  optional  ( TvmCell )) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l in 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload stateInit)) l) = true ->
  ETR_1 l' u dest value bounce allBalance payload stateInit. 
