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
Axiom LocalStateLRecord: Type.

Notation rec := LocalStateLRecord.
Axiom computed : LocalStateLRecord.  (*:= Eval compute in default. *)
#[global]
Instance def : XDefault LocalStateLRecord := {
  default := computed 
} . 
Definition VMStateDefault : VMStateLRecord  := Eval compute in default.
Definition LedgerDefault : LedgerLRecord LocalStateLRecord  := Eval compute in default. 

Definition incr_time (l: LedgerLRecord rec) (dt: N) :=
   let st := getPruvendoRecord Ledger_VMState l in 
   let t := getPruvendoRecord VMState_ι_now st in
   let newst := {$$ st with VMState_ι_now := Build_XUBInteger (uint2N t + dt) $$} in
   {$$ l with Ledger_VMState := newst $$}.

(* TODO: INT_1 *)

Definition INT_2 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false ->
  length_ owners > 0.

Definition INT_3 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  let MAX_CUSTODIANS := toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT rec def) ) l) in
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false ->
  length_ owners <= MAX_CUSTODIANS.

(* TODO: INT_4 *)

(* INT_5_1 is checked as part of INT_8_2 *)

(* TODO: INT_5_2 *)

Definition INT_6 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() || ) l) in
  let tvmPubkey := toValue (eval_state (sRReader || tvm->pubkey() || ) l) in
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false ->
  msgPubkey = tvmPubkey.

Definition INT_7 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  let l' := exec_state (Uinterpreter (constructor rec def owners reqConfirms)) l in 
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = true ->
  l' = l. (* TODO *)

Definition INT_8_1 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  let MAX_CUSTODIANS := toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() || ) l) in
  let tvmPubkey := toValue (eval_state (sRReader || tvm->pubkey() || ) l) in
  length_owners > 0 ->
  length_owners <= MAX_CUSTODIANS ->
  msgPubkey = tvmPubkey ->
  isError (eval_state (Uinterpreter (constructor rec def owners reqConfirms)) l) = false.

Definition INT_8_2 l (owners : mapping uint256 uint256) (reqConfirms :  uint8) : Prop := 
  let l' := exec_state (Uinterpreter (constructor rec def owners reqConfirms)) l in
  let owners_sz := length_ owners in
  let reqConfirms' := if reqConfirms < owners_sz then reqConfirms else owners_sz in
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
  N.land (toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l')) 0xFFFFFFFF = 0 /\
  (* result.m_transactions = {} *)
  toValue (eval_state (sRReader (m_transactions_right rec def) ) l') = [] /\
  (* result.m_custodianCount = params.owners.size *)
  toValue (eval_state (sRReader (m_custodianCount_right rec def) ) l') = owners_sz /\
  (* result.m_updateRequests = {} *)
  toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') = [] /\
  (* (∀ i : i ≥ 0 ⟶ i < 32 ⟶ result.m_updateRequestsMask[i] = false) *)
  N.land (toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) l')) 0xFFFFFFFF = 0.