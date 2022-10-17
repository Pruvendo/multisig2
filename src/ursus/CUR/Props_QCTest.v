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

Require Import  SetcodeMultisig. 

Definition CUR_1_propb l
        (codeHash : optional uint256) 
        (reqConfirms : optional uint8)
        (owners : optional (listArray uint256))
        (lifetime : optional uint32)
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
       codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CUR_1_propb.

Definition CUR_2_propb l
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8) 
        (lifetime : optional uint32)
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
       codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CUR_2_propb. 

Definition CUR_3_propb l
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8) 
        (lifetime : optional uint32)
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
       codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CUR_3_propb.

Definition CUR_4_propb l id
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8) 
        (lifetime : optional uint32)
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
       codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CUR_4_propb.

Definition CUR_5_propb l id
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8) 
        (lifetime : optional uint32)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

CUR_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
        id codeHash owners reqConfirms lifetime ? .

(* FAILS *)
QuickCheck CUR_5_propb.

Definition CUR_6_1_1_propb l tr1 tr2 tr3 tr4 
        (updateId :  uint64)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CUR_6_1_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        tr1 tr2 tr3 tr4 updateId ? .

(* Fail *)
QuickCheck CUR_6_1_1_propb.

Definition CUR_6_1_2_propb l tr1 tr2 tr3 tr4 
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8) 
        (lifetime :  optional uint32)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CUR_6_1_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        tr1 tr2 tr3 tr4 codeHash owners reqConfirms lifetime ? .

(* Fail *)
QuickCheck CUR_6_1_2_propb.

Definition CUR_6_1_3_propb l tr1 tr2 tr3 tr4 
        (transactionId :  uint64)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CUR_6_1_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        tr1 tr2 tr3 tr4 transactionId ? .

(* Fail *)
QuickCheck CUR_6_1_3_propb.

Definition CUR_6_1_4_propb l tr1 tr2 tr3 tr4 
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

CUR_6_1_4 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        tr1 tr2 tr3 tr4 dest value bounce allBalance payload stateInit ? .

(* Fail *)
QuickCheck CUR_6_1_4_propb.

Definition CUR_6_1_5_propb l tr1 tr2 tr3 tr4 
        (dest :  address) 
        (value :  uint128) 
        (bounce :  boolean) 
        (flags :  uint8)
        (payload :  cell_) 
        (mpk: uint256)
        (acc: bool)
        (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CUR_6_1_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
        tr1 tr2 tr3 tr4 dest value bounce flags payload  ? .

(* Fail *)
QuickCheck CUR_6_1_5_propb.

Definition CUR_7_propb l id
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256))
        (reqConfirms : optional uint8)
        (lifetime : optional uint32)
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
        id codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CUR_7_propb.