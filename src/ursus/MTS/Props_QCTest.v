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

Require Import  SetcodeMultisig. 

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
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

MTS_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
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
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

MTS_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
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
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

MTS_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
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
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

MTS_4 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
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
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

MTS_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
        id dest value bounce allBalance payload stateInit ? .

(* OK *)
QuickCheck MTS_5_propb.

Definition MTS_6_3_propb l
                (dest :  address) 
                (value :  uint128) 
                (bounce :  boolean) 
                (allBalance :  boolean) 
                (payload :  cell_)
                (stateInit :  optional TvmCell)
                (mpk: uint256)
                (acc: bool)
                timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let custodians : XHMap uint256 uint8 := getPruvendoRecord _m_custodians l in
let custodians' := if hmapIsMember mpk custodians then custodians 
else xHMapInsert mpk (Build_XUBInteger (length_ custodians)) custodians in

MTS_6_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians' $$}
        $$}with Ledger_VMState := v4 $$})
        dest value bounce allBalance payload stateInit  ? .

(* OK *)
QuickCheck MTS_6_3_propb.


Definition MTS_7_propb l
              (dest :  address) 
              (value :  uint128) 
              (bounce :  boolean) 
              (allBalance :  boolean) 
              (payload :  cell_)
              (stateInit :  optional TvmCell)
              (mpk: uint256)
              (acc: bool)
              timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := mpk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
MTS_7 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
        dest value bounce allBalance payload stateInit ? .

(* OK *)
QuickCheck MTS_7_propb.
