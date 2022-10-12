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

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import CommonQCEnvironment.
Require Import MTS.Props.
Require Import CommonForProps.

Require Import multisig2.

Definition MTS_1_propb l
        (dest :  address) 
        (value :  uint128) 
        (bounce :  boolean) 
        (allBalance :  boolean) 
        (payload :  cell_)
        (stateInit :  optional TvmCell) 
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

MTS_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
      dest value bounce allBalance payload stateInit ? .

(* OK *)
QuickCheck MTS_1_propb.


Definition MTS_2_propb l id
        (dest :  address) 
        (value :  uint128) 
        (bounce :  boolean) 
        (allBalance :  boolean) 
        (payload :  cell_)
        (stateInit :  optional TvmCell)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

MTS_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
      id dest value bounce allBalance payload stateInit ? .

(* OK *)
QuickCheck MTS_2_propb.

Definition MTS_3_propb l
        (dest :  address) 
        (value :  uint128) 
        (bounce :  boolean) 
        (allBalance :  boolean) 
        (payload :  cell_)
        (stateInit :  optional TvmCell)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

MTS_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        dest value bounce allBalance payload stateInit ? .

(* OK *)
QuickCheck MTS_3_propb.

Definition MTS_4_propb l id
        (dest :  address) 
        (value :  uint128) 
        (bounce :  boolean) 
        (allBalance :  boolean) 
        (payload :  cell_)
        (stateInit :  optional TvmCell)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

MTS_4 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        id dest value bounce allBalance payload stateInit ? .

(* OK *)
QuickCheck MTS_4_propb.

Definition MTS_5_propb l id
        (dest :  address) 
        (value :  uint128) 
        (bounce :  boolean) 
        (allBalance :  boolean) 
        (payload :  cell_)
        (stateInit :  optional TvmCell)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

MTS_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        id dest value bounce allBalance payload stateInit ? .

(* OK *)
QuickCheck MTS_5_propb.

Definition MTS_7_propb l id
              (dest :  address) 
              (value :  uint128) 
              (bounce :  boolean) 
              (allBalance :  boolean) 
              (payload :  cell_)
              (stateInit :  optional TvmCell)
              (mpk: uint256)
              (acc: bool)
              (pk: uint256)
              now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

MTS_7 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        id dest value bounce allBalance payload stateInit ? .

(* OK *)
QuickCheck MTS_7_propb.


Definition MTS_6_1_1_propb l tr1 tr2 tr3 tr4 
        (updateId :  uint64)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

MTS_6_1_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        tr1 tr2 tr3 tr4 updateId ? .

(* Fail *)
QuickCheck MTS_6_1_1_propb.

Definition MTS_6_1_2_propb l tr1 tr2 tr3 tr4 
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8) 
        (lifetime :  optional uint64 )
        (mpk: uint256)
        (acc: bool)
        (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

MTS_6_1_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        tr1 tr2 tr3 tr4 codeHash owners reqConfirms lifetime ? .

(* Fail *)
QuickCheck MTS_6_1_2_propb.

Definition MTS_6_1_3_propb l tr1 tr2 tr3 tr4 
        (transactionId :  uint64)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

MTS_6_1_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        tr1 tr2 tr3 tr4 transactionId ? .

(* Fail *)
QuickCheck MTS_6_1_3_propb.

Definition MTS_6_1_4_propb l tr1 tr2 tr3 tr4 
        (dest :  address) 
        (value :  uint128) 
        (bounce :  boolean) 
        (allBalance :  boolean) 
        (payload :  cell_) 
        (stateInit :  optional TvmCell )
        (mpk: uint256)
        (acc: bool)
        (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

MTS_6_1_4 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        tr1 tr2 tr3 tr4 dest value bounce allBalance payload stateInit ? .

(* Fail *)
QuickCheck MTS_6_1_4_propb.

Definition MTS_6_1_5_propb l tr1 tr2 tr3 tr4 
        (dest :  address) 
        (value :  uint128) 
        (bounce :  boolean) 
        (flags :  uint8)
        (payload :  cell_) 
        (stateInit :  optional TvmCell )
        (mpk: uint256)
        (acc: bool)
        (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

MTS_6_1_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        tr1 tr2 tr3 tr4 dest value bounce flags payload stateInit ? .

(* Fail *)
QuickCheck MTS_6_1_5_propb.