Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.
Require Import Coq.Program.Equality.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Require Import FinProof.All.
Require Import FinProof.CommonInstances.

Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Require Import UMLang.All.

Require Import UrsusStdLib.Solidity.All.

Require Import UrsusTVM.Solidity.All.

(* Require Import Blank.ClassTypesNotations. *)

(* Set Typeclasses Depth 100. *)

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

(* 

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.
 *)
Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import CommonQCEnvironment.
Require Import CUC.Props.
Require Import CommonForProps.

Require Import multisig.



Require Import UrsusStdLib.Solidity.All.
Require Import UrsusStdLib.Solidity.unitsNotations.
Require Import UrsusTVM.Solidity.All.
Require Import UrsusTVM.Solidity.UrsusDefinitions.
Require Import UrsusTVM.Solidity.ReverseTranslatorConstructions.
Print HasLength.

Definition CUC_5 l id (updateId :  uint64) (custodianIndex :  uint8) (code : cell_) (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop := 
  (* let l' := exec_state (Uinterpreter (executeUpdate rec def updateId code)) l in *)
  let l_res := exec_state (Uinterpreter (_confirmUpdate rec def updateId custodianIndex)) l in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let m_updateRequests_res := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l_res) in
  let u := xMaybeMapDefault (fun x => x) (hmapLookup id m_updateRequests) dummyRequest  in
  let u2 := xMaybeMapDefault (fun x => x) (hmapLookup id m_updateRequests_res) dummyRequest  in
  let confirmationsMask := getPruvendoRecord MultisigWallet_ι_UpdateRequest_ι_confirmationsMask u in 
  let confirmationsMask_2 := getPruvendoRecord MultisigWallet_ι_UpdateRequest_ι_confirmationsMask u2 in 
  let tr_id := getPruvendoRecord MultisigWallet_ι_UpdateRequest_ι_id u in 
  let signsReceived := uint2N (getPruvendoRecord MultisigWallet_ι_UpdateRequest_ι_signs u) in 
  let signsReceived_u2 := uint2N (getPruvendoRecord MultisigWallet_ι_UpdateRequest_ι_signs u2) in 
  let id_u2 := getPruvendoRecord MultisigWallet_ι_UpdateRequest_ι_id u2 in 
  correctState l ->
  hmapIsMember msgPubkey custodians = true ->
  hmapIsMember id m_updateRequests = true ->
  REU_1 l_res id codeHash owners reqConfirms ->
  tr_id = id -> 
  N.shiftl (uint2N id) (uint2N confirmationsMask) = 0 ->
  isError (eval_state (Uinterpreter (_confirmUpdate rec def updateId custodianIndex)) l) = false  /\
  (u2 <> u -> hmapIsMember id_u2 m_updateRequests = true -> hmapIsMember id_u2 m_updateRequests_res = true)
   /\ (N.shiftl (uint2N id_u2) (uint2N confirmationsMask_2) = 1). (* /\ signsReceived = signsReceived + 1). *)
  (* length_ m_updateRequests_res = length_ m_updateRequests. *)

  Definition CUC_5_propb l id (updateId :  uint64) (custodianIndex :  uint8) (code : cell_) (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8)
  (mpk: uint256)
  (acc: bool)
  (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CUC_5 (quickFixState {$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
                with Ledger_VMState := v2 $$})
id updateId custodianIndex code  codeHash owners reqConfirms ? .

(* FAILS *)
QuickCheck CUC_5_propb.

Definition CUC_1_propb l
(updateId :  uint64) (code : cell_)(mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

CUC_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
       updateId code ? .

(* OK *)
QuickCheck CUC_1_propb.

Definition CUC_2_propb l
id (updateId :  uint64) (code : cell_) (custodianIndex :  uint8) (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

CUC_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
       id updateId code custodianIndex codeHash owners reqConfirms  ? .

(* OK *)
QuickCheck CUC_2_propb.

Definition CUC_3_propb l
id (updateId :  uint64) (code : cell_) (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

CUC_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        id updateId code  codeHash owners reqConfirms  ? .

(* OK *)
QuickCheck CUC_3_propb.


Definition CUC_4_propb l id
(updateId :  uint64) (code : cell_) (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8)

              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

CUC_4 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
       id updateId code  codeHash owners reqConfirms  ? .

(* OK *)
QuickCheck CUC_4_propb.

Definition CUC_5_propb l id (updateId :  uint64) (custodianIndex :  uint8) (code : cell_) (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CUC_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        id updateId custodianIndex code  codeHash owners reqConfirms ? .

(* FAILS *)
QuickCheck CUC_5_propb.
