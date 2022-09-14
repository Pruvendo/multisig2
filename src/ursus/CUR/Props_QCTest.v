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
Require Import CUR.Props.
Require Import CommonForProps.

Require Import multisig.

Require Import UrsusStdLib.Solidity.All.
Require Import UrsusStdLib.Solidity.unitsNotations.
Require Import UrsusTVM.Solidity.All.
Require Import UrsusTVM.Solidity.UrsusDefinitions.
Require Import UrsusTVM.Solidity.ReverseTranslatorConstructions.

Definition CUR_5 l id (codeHash :  uint256) (owners :  listArray uint256) (reqConfirms :  uint8) : Prop := 
  let MAX_CUSTODIAN_COUNT := uint2N (toValue (eval_state (sRReader (MAX_CUSTODIAN_COUNT_right rec def) ) l)) in
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let msgPubkey := toValue (eval_state (sRReader || msg->pubkey() ) l) in
  let l' := exec_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l in
  let m_updateRequestsMask := (uint2N (toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) l'))) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  correctState l ->
  isError (eval_state (Uinterpreter (submitUpdate rec def codeHash owners reqConfirms)) l) = false ->
  hmapIsMember msgPubkey custodians = true ->
  length_ owners > 0 ->
  length_ owners <= MAX_CUSTODIAN_COUNT ->
  hmapIsMember id transactions = true ->
  REU_1 l' id codeHash owners reqConfirms ->
  N.land m_updateRequestsMask (uint2N id) = 0.

Definition CUR_5_propb l id
              (codeHash :  uint256) 
              (reqConfirms :  uint8)
              (owners : listArray uint256)
              (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in
CUR_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := {$$ l with  _m_custodians := custodians $$} $$}
                            with Ledger_VMState := v3 $$})

        id codeHash owners reqConfirms  ? .

(* FAILS *)
QuickCheck CUR_5_propb.


Definition CUR_1_propb l
              (codeHash :  uint256) 
              (reqConfirms :  uint8)
              (owners : listArray uint256)
              (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

CUR_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
       codeHash owners reqConfirms ? .

(* OK *)
QuickCheck CUR_1_propb.

Definition CUR_2_propb l
              (codeHash :  uint256) 
              (reqConfirms :  uint8)
              (owners : listArray uint256)
              (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

CUR_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
       codeHash owners reqConfirms  ? .

(* OK *)
QuickCheck CUR_2_propb.

Definition CUR_3_propb l
              (codeHash :  uint256) 
              (reqConfirms :  uint8)
              (owners : listArray uint256)
              (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

CUR_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
       codeHash owners reqConfirms  ? . 

(* OK *)
QuickCheck CUR_3_propb.


Definition CUR_4_propb l id
              (codeHash :  uint256) 
              (reqConfirms :  uint8)
              (owners : listArray uint256)
              (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

CUR_4 id (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
       codeHash owners reqConfirms  ? .

(* OK *)
QuickCheck CUR_4_propb.

Definition CUR_5_propb l id
              (codeHash :  uint256) 
              (reqConfirms :  uint8)
              (owners : listArray uint256)
              (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in
CUR_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := {$$ l with  _m_custodians := custodians $$} $$}
                            with Ledger_VMState := v3 $$})

        id codeHash owners reqConfirms  ? .

(* FAILS because while *)
QuickCheck CUR_5_propb.

Definition CUR_6_1_1_propb l req1 req2 req3 req4
              (updateId :  uint64)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
CUR_6_1_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        req1 req2 req3 req4 updateId ? .

(* Fail *)
QuickCheck CUR_6_1_1_propb.

Definition CUR_6_1_2_propb l req1 req2 req3 req4
              (codeHash :  uint256) 
              (owners :  listArray uint256) 
              (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
CUR_6_1_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        req1 req2 req3 req4 codeHash owners reqConfirms ? .

(* Fail *)
QuickCheck CUR_6_1_2_propb.

Definition CUR_6_1_3_propb l req1 req2 req3 req4
              (transactionId :  uint64)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
CUR_6_1_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        req1 req2 req3 req4 transactionId ? .

(* Fail *)
QuickCheck CUR_6_1_3_propb.

Definition CUR_6_1_4_propb l req1 req2 req3 req4
              (dest :  address) 
              (value :  uint128) 
              (bounce :  boolean) 
              (allBalance :  boolean) 
              (payload :  cell_)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
CUR_6_1_4 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        req1 req2 req3 req4 dest value bounce allBalance payload ? .

(* Fail *)
QuickCheck CUR_6_1_4_propb.

Definition CUR_6_1_5_propb l req1 req2 req3 req4
              (dest :  address) 
              (value :  uint128) 
              (bounce :  boolean) 
              (flags :  uint16) 
              (payload :  cell_)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
CUR_6_1_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        req1 req2 req3 req4 dest value bounce flags payload ? .

(* Fail *)
QuickCheck CUR_6_1_5_propb.


Definition CUR_7_propb l id
              (codeHash :  uint256) 
              (reqConfirms :  uint8)
              (owners : listArray uint256)
              (reqConfirms :  uint8)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

CUR_7 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        id codeHash owners reqConfirms  ? .

(* OK *)
QuickCheck CUR_7_propb.