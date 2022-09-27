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
Require Import STS.Props.
Require Import CommonForProps.

Require Import multisig2.

Definition STS_1_propb l
            (dest :  address) 
            (value :  uint128)
            (bounce :  boolean)
            (flags :  uint16)
            (payload :  cell_) 
            (mpk: uint256)
            (acc: bool)
            (bal: N)
            now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

STS_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
       dest value bounce flags payload  ? .

(* OK *)
QuickCheck STS_1_propb.

Definition STS_2_propb l
            (dest :  address) 
            (value :  uint128)
            (bounce :  boolean)
            (flags :  uint16)
            (payload :  cell_) 
            (mpk: uint256)
            (acc: bool)
            (bal: N)
            now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in

STS_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v3 $$})
       dest value bounce flags payload  ? .

(* OK *)
QuickCheck STS_2_propb.

Definition STS_3_1_propb l
            (dest :  address) 
            (value :  uint128)
            (bounce :  boolean)
            (flags :  uint16)
            (payload :  cell_) 
            (mpk: uint256)
            (acc: bool)
            (bal: N)
            now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

STS_3_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v3 $$})
       dest value bounce flags payload  ? .

(* OK *)
QuickCheck STS_3_1_propb.

Definition STS_3_2_propb l
            (dest :  address) 
            (value :  uint128)
            (bounce :  boolean)
            (flags :  uint16)
            (payload :  cell_) 
            (mpk: uint256)
            (acc: bool)
            (bal: N)
            now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

STS_3_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v3 $$})
       dest value bounce flags payload  ? .

(* OK *)
QuickCheck STS_3_2_propb.