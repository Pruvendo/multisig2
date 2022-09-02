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

Definition MTC_1 l (transactionId :  uint64) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false ->
  hmapIsMember msgPubkey custodians = true.

(* TODO: MTC_2 (need ETR1) *)

Definition dummyTransaction : MultisigWallet_ι_TransactionLRecord := Eval compute in default. 

Definition MTC_3 l (transactionId :  uint64) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transaction := hmapFindWithDefault dummyTransaction transactionId transactions in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  let mask := uint2N (getPruvendoRecord MultisigWallet_ι_Transaction_ι_confirmationsMask transaction) in
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false ->
  N.land mask (N.shiftl 1 i) = 0.

Definition MTC_4 l (transactionId :  uint64) : Prop := 
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transaction := hmapFindWithDefault dummyTransaction transactionId transactions in
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false ->
  hmapIsMember transactionId transactions = true /\
  getPruvendoRecord MultisigWallet_ι_Transaction_ι_id transaction = transactionId.

Definition MTC_5_1 l (transactionId : uint64) : Prop :=
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transaction := hmapFindWithDefault dummyTransaction transactionId transactions in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  let mask := uint2N (getPruvendoRecord MultisigWallet_ι_Transaction_ι_confirmationsMask transaction) in
  correctState l ->
  hmapIsMember msgPubkey custodians = true ->
  hmapIsMember transactionId transactions = true ->
  N.land mask (N.shiftl 1 i) = 0 ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false.

(* TODO: add ETR1 *)
Definition MTC_5_2 l (transactionId :  uint64) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transaction := hmapFindWithDefault dummyTransaction transactionId transactions in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  let mask := uint2N (getPruvendoRecord MultisigWallet_ι_Transaction_ι_confirmationsMask transaction) in
  let requiredConfirmations := uint2N (toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l)) in
  let signsReceived := uint2N (getPruvendoRecord MultisigWallet_ι_Transaction_ι_signsReceived transaction) in
  let l' := exec_state (Uinterpreter (confirmTransaction rec def transactionId)) l in 
  let transactions' := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let transaction' := hmapFindWithDefault dummyTransaction transactionId transactions' in
  let signsReceived' := uint2N (getPruvendoRecord MultisigWallet_ι_Transaction_ι_signsReceived transaction') in
  let mask' := uint2N (getPruvendoRecord MultisigWallet_ι_Transaction_ι_confirmationsMask transaction') in
  let commonTransactions := xHMapFilter (fun k v => 
    andb (hmapIsMember k transactions)
    (eqb v (hmapFindWithDefault dummyTransaction k transactions))) transactions' in
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false ->
  requiredConfirmations > signsReceived + 1 ->
  hmapIsMember transactionId transactions' = true /\
  signsReceived' = signsReceived + 1 /\
  mask' = N.lor mask (N.shiftl 1 i) /\
  length_ transactions' = length_ transactions /\
  length_ commonTransactions = length_ transactions - 1
  .

(* TODO: add ETR1 *)
Definition MTC_6 l (transactionId :  uint64) : Prop := 
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transaction := hmapFindWithDefault dummyTransaction transactionId transactions in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let i := uint2N (hmapFindWithDefault (Build_XUBInteger 0) msgPubkey custodians) in
  let mask := uint2N (getPruvendoRecord MultisigWallet_ι_Transaction_ι_confirmationsMask transaction) in
  let requiredConfirmations := uint2N (toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l)) in
  let signsReceived := uint2N (getPruvendoRecord MultisigWallet_ι_Transaction_ι_signsReceived transaction) in
  let l' := exec_state (Uinterpreter (confirmTransaction rec def transactionId)) l in 
  let transactions' := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let commonTransactions := xHMapFilter (fun k v => 
    andb (hmapIsMember k transactions)
    (eqb v (hmapFindWithDefault dummyTransaction k transactions))) transactions' in
  let messageQueueDefault := (toValue (eval_state (sRReader (ULtoRValue ( IDefault_left rec def ))) l')) in
  let messageQueueTmp := (toValue (eval_state (sRReader (ULtoRValue ( Itmp_left rec def ))) l'))  in 
  let dest := getPruvendoRecord MultisigWallet_ι_Transaction_ι_dest transaction in
  let value := getPruvendoRecord MultisigWallet_ι_Transaction_ι_value transaction in
  let bounce := getPruvendoRecord MultisigWallet_ι_Transaction_ι_bounce transaction in
  let flags := getPruvendoRecord MultisigWallet_ι_Transaction_ι_sendFlags transaction in
  let payload := getPruvendoRecord MultisigWallet_ι_Transaction_ι_payload transaction in
  let mes := (EmptyMessage IDefault (value, (bounce, (flags, payload)))) in
  correctState l ->
  isError (eval_state (Uinterpreter (confirmTransaction rec def transactionId)) l) = false ->
  requiredConfirmations <= signsReceived + 1 ->
  length_ transactions' = length_ transactions - 1 /\
  length_ commonTransactions = length_ transactions' /\
  hmapIsMember transactionId transactions' = false /\
  isOnlyMessage messageQueueDefault = true /\
  length_ messageQueueTmp = 0 /\
  isMessageSent mes dest 0 messageQueueDefault = true.