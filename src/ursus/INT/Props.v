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

Definition INT_1 l (owners : listArray uint256) (reqConfirms :  uint8) : Prop := 
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false ->
  length_ owners > 0.

Definition INT_2 l (owners : listArray uint256) (reqConfirms :  uint8) : Prop := 
  let MAX_CUSTODIANS := toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l) in
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false ->
  length_ owners <= uint2N MAX_CUSTODIANS.

(* --constructor--
   --executeUpdate--
   1: confirmUpdate
   2: submitUpdate
   3: confirmTransaction
   4: submitTransaction
   5: sendTransaction 
*)

Definition INT_3_common l l': Prop :=
  toValue (eval_state (sRReader (m_custodians_right rec def) ) l) =
    toValue (eval_state (sRReader (m_custodians_right rec def) ) l') /\
  toValue (eval_state (sRReader (m_custodianCount_right rec def) ) l) =
    toValue (eval_state (sRReader (m_custodianCount_right rec def) ) l') /\
  toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l) =
    toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l') /\
  (* INT_5_2 *)
  toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l) =
    toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l').

Definition INT_3_1 l (updateId :  uint64) : Prop :=
  let l' := exec_state (Uinterpreter (confirmUpdate rec def updateId)) l in 
  correctState l ->
  INT_3_common l l'.

Definition INT_3_2 l (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop :=
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l in 
  correctState l ->
  INT_3_common l l'.

Definition INT_3_3 l (transactionId :  uint64) : Prop :=
  let l' := exec_state (Uinterpreter (confirmTransaction rec def transactionId)) l in 
  correctState l ->
  INT_3_common l l'.

Definition INT_3_4 l (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l in 
  correctState l ->
  INT_3_common l l'.

Definition INT_3_5 l (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint16) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (sendTransaction rec def dest value bounce flags payload)) l in 
  correctState l ->
  INT_3_common l l'.

(* INT_4_1 is checked as part of INT_7_2 *)

(* INT_4_2 is checked as part of INT_3_x *)

Definition INT_5 l (owners : listArray uint256) (reqConfirms :  uint8) : Prop := 
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey()  ) l) in
  let tvmPubkey := toValue (eval_state (sRReader || tvm->pubkey() ) l) in
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false ->
  msgPubkey = tvmPubkey.

Definition INT_6 (l: LedgerLRecord rec) (owners : listArray uint256) (reqConfirms :  uint8) : Prop := 
  let l' := exec_state (Uinterpreter (constructor rec def owners reqConfirms)) l in 
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = true ->
  ledgerEqb l l' = true. 

Definition INT_7_1 l (owners : listArray uint256) (reqConfirms :  uint8) : Prop := 
  let MAX_CUSTODIANS := toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let tvmPubkey := toValue (eval_state (sRReader || tvm->pubkey() ) l) in
  length_ owners > 0 ->
  length_ owners <= uint2N MAX_CUSTODIANS ->
  msgPubkey = tvmPubkey ->
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false.

Definition checkMap' (m: XHMap ( uint256 )( uint8 )) (i: N) (k: option uint256) := 
  let k' := xMaybeMapDefault id k (Build_XUBInteger 0) in
  let with_i := xHMapFilter (fun _k v => Common.eqb v (Build_XUBInteger i)) m in 
  andb 
    (andb (xMaybeIsSome k) (hmapIsMember k' m))
    ((eqb (length_ with_i) 1)).

Fixpoint checkMap m n (owners: listArray uint256):= 
  match n with 
  | O => true
  | S n' => andb (checkMap m n' owners) (checkMap' m (N.of_nat n') (arrLookup (N.of_nat n') owners))
  end.

Definition INT_7_2 l (owners : listArray uint256) (reqConfirms :  uint8) : Prop := 
  let l' := exec_state (Uinterpreter (constructor rec def owners reqConfirms)) l in
  let owners_sz := length_ owners in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l') in
  let custodians_sz := length_ custodians in
  let reqConfirms' := if N.ltb custodians_sz owners_sz then (Build_XUBInteger custodians_sz) else (Build_XUBInteger owners_sz) in
  let ownerKey := toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l') in
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false ->
  (* result.m_custodians.size <= params.owners.size *)
  custodians_sz <= owners_sz /\
  checkMap custodians (N.to_nat owners_sz) owners = true /\
  (* result.m_defaultRequiredConfirmations = min (result.this.m_custodians.size, params.reqConfirms) *)
  toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l') = reqConfirms' /\
  (* result.m_ownerKey = params.this.owners[0] *)
  Some ownerKey = arrLookup 0 owners /\
  (* (∀ i : i ≥ 0 ⟶ i < 32 ⟶ result.m_requestsMask[i] = false) *)
  N.land 
    (uint2N (toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l')))
     0xFFFFFFFF = 0 /\
  (* result.m_transactions = {} *)
  length_ (toValue (eval_state (sRReader (m_transactions_right rec def) ) l')) = 0 /\
  (* result.m_updateRequests = {} *)
  length_ (toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l')) = 0 /\
  (* (∀ i : i ≥ 0 ⟶ i < 32 ⟶ result.m_updateRequestsMask[i] = false) *)
  N.land 
    (uint2N (toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) l')))
     0xFFFFFFFF = 0.