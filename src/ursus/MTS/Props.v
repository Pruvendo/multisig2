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

Definition ETR_1 l u (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop := 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let EXPIRATION_TIME := uint2N (toValue (eval_state (sRReader (EXPIRATION_TIME_right rec def) ) l)) in
  let MAX_CLEANUP_TXNS := uint2N (toValue (eval_state (sRReader (MAX_CLEANUP_TXNS_right rec def) ) l)) in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let id := (getPruvendoRecord MultisigWallet_ι_Transaction_ι_id u) in
  let l' := exec_state (Uinterpreter (_removeExpiredTransactions rec def)) l in 
  let m_transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l) = false -> 
  hmapIsMember id m_updateRequests = true ->
  (N.shiftr (uint2N id) 32) + EXPIRATION_TIME <= tvm_now  ->
  length_ (xHMapFilter (fun _k t => (eqb (getPruvendoRecord MultisigWallet_ι_Transaction_ι_id t) id)) transactions) < MAX_CLEANUP_TXNS  <->
  hmapIsMember id transactions = true /\
  hmapIsMember id m_transactions = false.


Definition MTS_1 l (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l) = false ->
  hmapIsMember msgPubkey custodians = true.

Definition MTS_2 l id (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l in 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l) = true ->
  hmapIsMember msgPubkey custodians = true ->
  hmapIsMember id transactions = true -> 
  ETR_1 l' u dest value bounce allBalance payload. 

Definition MTS_3 l id (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let requestsMask := toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l) in 
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in  
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l in 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l) = false ->
  hmapIsMember msgPubkey custodians = true -> 
  ETR_1 l' u dest value bounce allBalance payload -> 
  uint2N requestsMask < 5. 

Definition MTS_4 l id (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop := 
  let FLAG_IGNORE_ERRORS := uint2N (toValue (eval_state (sRReader (FLAG_IGNORE_ERRORS_right rec def) ) l)) in
  let FLAG_SEND_ALL_REMAINING := uint2N (toValue (eval_state (sRReader (FLAG_SEND_ALL_REMAINING_right rec def) ) l)) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let requestsMask := uint2N (toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l)) in (* ???? *)
  let m_defaultRequiredConfirmations :=  uint2N (toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l)) in (* ???? *)
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l in
  let messqueue := toValue ((eval_state (sRReader (ULtoRValue (IDefault_left rec def)))) l') in 
  let mes := EmptyMessage IDefault (Build_XUBInteger 0, (bounce, (Build_XUBInteger (N.lor FLAG_IGNORE_ERRORS FLAG_SEND_ALL_REMAINING) , payload))) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l) = false ->
  hmapIsMember msgPubkey custodians = true -> 
  ETR_1 l' u dest value bounce allBalance payload -> 
  requestsMask < 5 -> 
  m_defaultRequiredConfirmations < 2 ->
  allBalance = true ->
  isOnlyMessage messqueue = true /\
  isMessageSent mes dest 0 messqueue = true . 


Definition MTS_5 l id (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop := 
  let FLAG_IGNORE_ERRORS := uint2N (toValue (eval_state (sRReader (FLAG_IGNORE_ERRORS_right rec def) ) l)) in
  let FLAG_PAY_FWD_FEE_FROM_BALANCE := uint2N (toValue (eval_state (sRReader (FLAG_PAY_FWD_FEE_FROM_BALANCE_right rec def) ) l)) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let requestsMask := uint2N (toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l)) in (* ???? *)
  let m_defaultRequiredConfirmations :=  uint2N (toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l)) in (* ???? *)
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l in
  let messqueue := toValue ((eval_state (sRReader (ULtoRValue (IDefault_left rec def)))) l') in 
  let mes := EmptyMessage IDefault (value, (bounce, ((Build_XUBInteger  (N.lor FLAG_IGNORE_ERRORS FLAG_PAY_FWD_FEE_FROM_BALANCE)), payload))) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l) = false ->
  hmapIsMember msgPubkey custodians = true -> 
  ETR_1 l' u dest value bounce allBalance payload -> 
  requestsMask < 5 -> 
  m_defaultRequiredConfirmations < 2 ->
  allBalance = false ->
  isOnlyMessage messqueue = true /\
  isMessageSent mes dest 0 messqueue = true . 


Definition MTS_7 l id (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l in 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l) = true ->
  ETR_1 l' u dest value bounce allBalance payload. 

Definition MTS_6_1_common l l' tr1 tr2 tr3 tr4: Prop := 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transactions_2 := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let id1 := getPruvendoRecord MultisigWallet_ι_Transaction_ι_id tr1 in
  let id2 := getPruvendoRecord MultisigWallet_ι_Transaction_ι_id tr2 in
  let id3 := getPruvendoRecord MultisigWallet_ι_Transaction_ι_id tr3 in
  let id4 := getPruvendoRecord MultisigWallet_ι_Transaction_ι_id tr4 in 
  tr1 <> tr2 ->
  hmapIsMember id1 transactions = true ->
  hmapIsMember id2 transactions = true ->
  id1 <> id2 ->
  tr3 <> tr4 ->
  hmapIsMember id3 transactions_2 = true ->
  hmapIsMember id4 transactions_2 = true ->
  id3 <> id4.


Definition MTS_6_1_1 l tr1 tr2 tr3 tr4 (updateId :  uint64) : Prop :=
  let l' := exec_state (Uinterpreter (confirmUpdate rec def updateId)) l in 
  correctState l ->
  MTS_6_1_common l l' tr1 tr2 tr3 tr4.

Definition MTS_6_1_2 l tr1 tr2 tr3 tr4 (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop :=
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l in 
  correctState l ->
  MTS_6_1_common l l' tr1 tr2 tr3 tr4.

Definition MTS_6_1_3 l tr1 tr2 tr3 tr4 (transactionId :  uint64) : Prop :=
  let l' := exec_state (Uinterpreter (confirmTransaction rec def transactionId)) l in 
  correctState l ->
  MTS_6_1_common l l' tr1 tr2 tr3 tr4.

Definition MTS_6_1_4 l tr1 tr2 tr3 tr4 (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l in 
  correctState l ->
  MTS_6_1_common l l' tr1 tr2 tr3 tr4.

Definition MTS_6_1_5 l tr1 tr2 tr3 tr4 (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint16) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (sendTransaction rec def dest value bounce flags payload)) l in 
  correctState l ->
  MTS_6_1_common l l' tr1 tr2 tr3 tr4.