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

Definition ETR_1 l u: Prop := 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  let MAX_CLEANUP_TXNS := uint2N (toValue (eval_state (sRReader (MAX_CLEANUP_TXNS_right rec def) ) l)) in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let id := (getPruvendoRecord Transaction_ι_id u) in
  let l' := exec_state (Uinterpreter (_removeExpiredTransactions rec def)) l in 
  let m_transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  hmapIsMember id m_updateRequests = true ->
  (N.shiftl (uint2N id) 32) + lifetime <= tvm_now  ->
  length_ (xHMapFilter (fun _k t => (eqb (getPruvendoRecord Transaction_ι_id t) id)) transactions) < MAX_CLEANUP_TXNS  <->
  hmapIsMember id transactions = true /\
  hmapIsMember id m_transactions = false.


Definition MTC_1 l (transactionId :  uint64) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false ->
  hmapIsMember msgPubkey custodians = true.

Definition dummyTransaction : TransactionLRecord := Eval compute in default. 

Definition MTC_2 l (transactionId :  uint64) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (confirmTransaction rec def transactionId)) l in 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup transactionId transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = true ->
  hmapIsMember msgPubkey custodians = true ->
  hmapIsMember transactionId transactions = true -> 
  ETR_1 l' u. 

Definition MTC_3 l (transactionId :  uint64) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transaction := hmapFindWithDefault dummyTransaction transactionId transactions in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  let mask := uint2N (getPruvendoRecord Transaction_ι_confirmationsMask transaction) in
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false ->
  N.land mask (N.shiftl 1 i) = 0.

Definition MTC_4 l (transactionId :  uint64) : Prop := 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transaction := hmapFindWithDefault dummyTransaction transactionId transactions in
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false ->
  hmapIsMember transactionId transactions = true /\
  getPruvendoRecord Transaction_ι_id transaction = transactionId.

Definition MTC_5_1 l (transactionId : uint64) : Prop :=
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transaction := hmapFindWithDefault dummyTransaction transactionId transactions in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  let mask := uint2N (getPruvendoRecord Transaction_ι_confirmationsMask transaction) in
  let lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let id := (getPruvendoRecord Transaction_ι_id transaction) in
  correctState l ->
  hmapIsMember msgPubkey custodians = true ->
  hmapIsMember transactionId transactions = true ->
  N.land mask (N.shiftl 1 i) = 0 ->
  (N.shiftr (uint2N id) 32) + lifetime > tvm_now  ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false.


Definition MTC_5_2 l id (transactionId :  uint64) (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) (stateInit :  optional  ( TvmCell )) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transaction := hmapFindWithDefault dummyTransaction transactionId transactions in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  let mask := uint2N (getPruvendoRecord Transaction_ι_confirmationsMask transaction) in
  let requiredConfirmations := uint2N (getPruvendoRecord Transaction_ι_signsRequired transaction) in
  let signsReceived := uint2N (getPruvendoRecord Transaction_ι_signsReceived transaction) in
  let l' := exec_state (Uinterpreter (confirmTransaction rec def transactionId)) l in 
  let transactions' := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let transaction' := hmapFindWithDefault dummyTransaction transactionId transactions' in
  let signsReceived' := uint2N (getPruvendoRecord Transaction_ι_signsReceived transaction') in
  let mask' := uint2N (getPruvendoRecord Transaction_ι_confirmationsMask transaction') in
  let lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let expiredTransactions := xHMapFilter (fun k v =>
    N.leb ((N.shiftr (uint2N k) 32) + lifetime) tvm_now
  ) transactions in
  let commonTransactions := xHMapFilter (fun k v => 
    andb (hmapIsMember k transactions)
    (Common.eqb v (hmapFindWithDefault dummyTransaction k transactions))) transactions' in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false ->
  requiredConfirmations > signsReceived + 1 ->
  hmapIsMember transactionId transactions' = true /\
  signsReceived' = signsReceived + 1 /\
  mask' = N.lor mask (N.shiftl 1 i) /\
  length_ transactions' = length_ transactions - length_ expiredTransactions /\
  length_ commonTransactions = length_ transactions - 1 - length_ expiredTransactions
  .

Definition MTC_6 l id (transactionId :  uint64) (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) (stateInit :  optional  ( TvmCell )): Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transaction := hmapFindWithDefault dummyTransaction transactionId transactions in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  let mask := uint2N (getPruvendoRecord Transaction_ι_confirmationsMask transaction) in
  let requiredConfirmations := uint2N (getPruvendoRecord Transaction_ι_signsRequired transaction) in
  let signsReceived := uint2N (getPruvendoRecord Transaction_ι_signsReceived transaction) in
  let lifetime := uint2N (toValue (eval_state (sRReader (m_lifetime_right rec def) ) l)) in
  let tvm_now := uint2N (toValue (eval_state (sRReader || now ) l)) in
  let l' := exec_state (Uinterpreter (confirmTransaction rec def transactionId)) l in 
  let transactions' := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let expiredTransactions := xHMapFilter (fun k v =>
    N.leb ((N.shiftr (uint2N k) 32) + lifetime) tvm_now
  ) transactions in
  let commonTransactions := xHMapFilter (fun k v => 
    andb (hmapIsMember k transactions)
    (eqb v (hmapFindWithDefault dummyTransaction k transactions))) transactions' in
  let messageQueueDefault := (toValue (eval_state (sRReader (ULtoRValue ( IDefault_left rec def ))) l')) in
  let dest := getPruvendoRecord Transaction_ι_dest transaction in
  let value := getPruvendoRecord Transaction_ι_value transaction in
  let bounce := getPruvendoRecord Transaction_ι_bounce transaction in
  let flags := getPruvendoRecord Transaction_ι_sendFlags transaction in
  let payload := getPruvendoRecord Transaction_ι_payload transaction in
  let mes := (EmptyMessage IDefault (value, (bounce, (flags, payload)))) in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id transactions) dummyTransaction  in  
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false ->
  requiredConfirmations <= signsReceived + 1 ->
  length_ transactions' = length_ transactions - 1 - length_ expiredTransactions /\
  length_ commonTransactions = length_ transactions' - length_ expiredTransactions /\
  hmapIsMember transactionId transactions' = false /\
  isOnlyMessage messageQueueDefault = true /\
  isMessageSent mes dest 0 messageQueueDefault = true.