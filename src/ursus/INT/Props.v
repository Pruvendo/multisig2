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

(* TODO: INT_1 *)

Definition INT_2 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false ->
  length_ owners > 0.

Definition INT_3 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
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

Definition INT_4_common l l': Prop :=
  toValue (eval_state (sRReader (m_custodians_right rec def) ) l) =
    toValue (eval_state (sRReader (m_custodians_right rec def) ) l') /\
  toValue (eval_state (sRReader (m_custodianCount_right rec def) ) l) =
    toValue (eval_state (sRReader (m_custodianCount_right rec def) ) l') /\
  toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l) =
    toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l') /\
  (* INT_5_2 *)
  toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l) =
    toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l').

Definition INT_4_1 l (updateId :  uint64) : Prop :=
  let l' := exec_state (Uinterpreter (confirmUpdate rec def updateId)) l in 
  correctState l ->
  INT_4_common l l'.

Definition INT_4_2 l (codeHash :  uint256) (owners :  mapping uint256 uint256) (reqConfirms :  uint8) : Prop :=
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l in 
  correctState l ->
  INT_4_common l l'.

Definition INT_4_3 l (transactionId :  uint64) : Prop :=
  let l' := exec_state (Uinterpreter (confirmTransaction rec def transactionId)) l in 
  correctState l ->
  INT_4_common l l'.

Definition INT_4_4 l (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (submitTransaction rec def dest value bounce allBalance payload)) l in 
  correctState l ->
  INT_4_common l l'.

Definition INT_4_5 l (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint16) (payload :  cell_) : Prop :=
  let l' := exec_state (Uinterpreter (sendTransaction rec def dest value bounce flags payload)) l in 
  correctState l ->
  INT_4_common l l'.

(* INT_5_1 is checked as part of INT_8_2 *)

(* INT_5_2 is checked as part of INT_4_x *)

Definition INT_6 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey()  ) l) in
  let tvmPubkey := toValue (eval_state (sRReader || tvm->pubkey() ) l) in
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false ->
  msgPubkey = tvmPubkey.

Definition INT_7 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  let l' := exec_state (Uinterpreter (constructor rec def owners reqConfirms)) l in 
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = true ->
  l' = l. (* TODO? *)

Definition INT_8_1 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  let MAX_CUSTODIANS := toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let tvmPubkey := toValue (eval_state (sRReader || tvm->pubkey() ) l) in
  length_ owners > 0 ->
  length_ owners <= uint2N MAX_CUSTODIANS ->
  msgPubkey = tvmPubkey ->
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false.

Definition INT_8_2 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  let l' := exec_state (Uinterpreter (constructor rec def owners reqConfirms)) l in
  let owners_sz := length_ owners in
  let reqConfirms' := if N.ltb (uint2N reqConfirms) owners_sz then reqConfirms else (Build_XUBInteger owners_sz) in
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false ->
  (* result.initialized = true *)
  (* ??? *)
  (* result.m_custodians.size = params.owners.size *)
  length_ (toValue (eval_state (sRReader (m_custodians_right rec def) ) l')) = owners_sz /\
  (* (∀ i : i ≥ 0 ⟶ i < params.owners.size ⟶ (result.m_custodians[i].exists ⋀ result.m_custodians[i].value = params.owners[i])) *)
  (* ??? *)
  (* result.m_defaultRequiredConfirmations = min (params.owners.size, params.reqConfirms) *)
  toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l') = reqConfirms' /\
  (* result.m_ownerKey = params.this.creator.pubkey *)
  (* ??? *)
  (* (∀ i : i ≥ 0 ⟶ i < 32 ⟶ result.m_requestsMask[i] = false) *)
  N.land 
    (uint2N (toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l')))
     0xFFFFFFFF = 0 /\
  (* result.m_transactions = {} *)
  toValue (eval_state (sRReader (m_transactions_right rec def) ) l') = wrap Map Datatypes.nil /\
  (* result.m_custodianCount = params.owners.size *)
  uint2N (toValue (eval_state (sRReader (m_custodianCount_right rec def) ) l')) = owners_sz /\
  (* result.m_updateRequests = {} *)
  toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') = wrap Map Datatypes.nil /\
  (* (∀ i : i ≥ 0 ⟶ i < 32 ⟶ result.m_updateRequestsMask[i] = false) *)
  N.land 
    (uint2N (toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) l')))
     0xFFFFFFFF = 0.