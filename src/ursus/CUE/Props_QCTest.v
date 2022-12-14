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
Require Import CUE.Props.
Require Import CommonForProps.

Require Import  SetcodeMultisig. 

Definition CUE_1_propb l
        (updateId :  uint64) 
        (code : optional cell_)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
CUE_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
        updateId code  ? .

(* OK *)
QuickCheck CUE_1_propb.

Definition CUE_2_propb l id
        (updateId :  uint64) 
        (code : optional cell_) 
        (custodianIndex :  uint8) 
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8)
        (lifetime : optional uint32)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CUE_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
        id updateId code custodianIndex codeHash owners reqConfirms lifetime ? .

(* fails SOMETIMES *)

QuickCheck CUE_2_propb.

Definition CUE_3_propb l id
        (updateId :  uint64)
        (code : optional cell_) 
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8)
        (lifetime : optional uint32)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CUE_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
        id updateId code codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CUE_3_propb.


Definition CUE_4_propb l id
        (updateId :  uint64)
        (code : optional cell_) 
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8)
        (lifetime : optional uint32)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CUE_4  (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
        id updateId code codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CUE_4_propb.

Definition CUE_6_2_propb l
        (updateId :  uint64)
        (code : optional cell_) 
        (mpk: uint256)
        (acc: bool)
        (update: UpdateRequestLRecord)
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

let updates := getPruvendoRecord _m_updateRequests l in
let updates' := if hmapIsMember updateId updates then updates 
else xHMapInsert updateId update updates in


CUE_6_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
        {$$ l with _m_updateRequests := updates' $$} $$}
                            with Ledger_VMState := v4 $$})
        updateId code ? .

(* OK *)
QuickCheck CUE_6_2_propb.