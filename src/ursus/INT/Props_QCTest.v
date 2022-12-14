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
Require Import INT.Props.
Require Import CommonForProps.

Require Import  SetcodeMultisig. 

Definition INT_1_propb
       (owners : listArray uint256)
       (reqConfirms :  uint8)
       (lifetime :  uint32)
       (mpk: uint256)
       (acc: bool)
       (pk: uint256)
       timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

INT_1 {$$ LedgerDefault with Ledger_VMState := v4 $$}
       owners reqConfirms lifetime ? .

(* OK *)
QuickCheck INT_1_propb.

Definition INT_2_propb
       (owners : listArray uint256)
       (reqConfirms :  uint8)
       (lifetime :  uint32)
       (mpk: uint256)
       (acc: bool)
       (pk: uint256)
       timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

INT_2 {$$ LedgerDefault with Ledger_VMState := v4 $$}
       owners reqConfirms lifetime ? .

(* OK *)
QuickCheck INT_2_propb.

Definition INT_3_1_propb l
       (updateId :  uint64)
       (mpk: uint256)
       (acc: bool)
       (bal: N)
       timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

INT_3_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v4 $$})
       updateId  ? .

(* OK *)
QuickCheck INT_3_1_propb.

Definition INT_3_2_propb l
       (codeHash : optional uint256) 
       (owners : optional (listArray uint256)) 
       (reqConfirms : optional uint8)
       (lifetime : optional uint32)
       (mpk: uint256)
       (acc: bool)
       (bal: N)
       timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

INT_3_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v4 $$})
       codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck INT_3_2_propb.

Definition INT_3_3_propb l
       (transactionId :  uint64)
       (mpk: uint256)
       (acc: bool)
       (bal: N)
       timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

INT_3_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v4 $$})
       transactionId  ? .

(* OK *)
QuickCheck INT_3_3_propb.

Definition INT_3_4_propb l
       (dest :  address) 
       (value :  uint128) 
       (bounce :  boolean) 
       (allBalance :  boolean) 
       (payload :  cell_)
       (stateInit :  optional TvmCell)
       (mpk: uint256)
       (acc: bool)
       (bal: N)
       timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

INT_3_4 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v4 $$})
       dest value bounce allBalance payload stateInit ? .

(* OK *)
QuickCheck INT_3_4_propb.

Definition INT_3_5_propb l
       (dest :  address) 
       (value :  uint128)
       (bounce :  boolean)
       (flags :  uint8)
       (payload :  cell_) 
       (mpk: uint256)
       (acc: bool)
       (bal: N)
       timestamp
       now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

INT_3_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v4 $$})
       dest value bounce flags payload  ? .

(* OK *)
QuickCheck INT_3_5_propb.

Definition INT_6_propb
       (owners : listArray uint256)
       (reqConfirms :  uint8)
       (lifetime :  uint32)
       (mpk: uint256)
       (acc: bool)
       (pk: uint256)
       timestamp
       now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

INT_6 {$$ LedgerDefault with Ledger_VMState := v4 $$}
       owners reqConfirms lifetime ? .

(* OK *)
QuickCheck INT_6_propb.

Definition INT_7_propb
       (owners : listArray uint256)
       (reqConfirms :  uint8)
       (lifetime :  uint32)
       (acc: bool)
       (pk: uint256)
       timestamp
       now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

INT_7 {$$ LedgerDefault with Ledger_VMState := v4 $$}
       owners reqConfirms lifetime ? .

(* OK *)
QuickCheck INT_7_propb.

Definition INT_8_1_propb
       (owners : listArray uint256)
       (reqConfirms :  uint8)
       (lifetime :  uint32)
       (acc: bool)
       (pk: uint256)
       timestamp
       now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

INT_8_1 {$$ LedgerDefault with Ledger_VMState := v4 $$}
       owners reqConfirms lifetime ? .

(* OK *)
QuickCheck INT_8_1_propb.

Definition INT_8_2_propb
            (owners : listArray uint256)
            (reqConfirms :  uint8)
            (lifetime :  uint32)
            (acc: bool)
            (pk: uint256)
            timestamp
            (now:N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

INT_8_2 {$$ LedgerDefault with Ledger_VMState := v4 $$}
       owners reqConfirms lifetime ? .

(* OK *)
QuickCheck INT_8_2_propb.