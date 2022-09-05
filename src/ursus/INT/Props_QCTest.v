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

Require Import multisig.

Definition INT_1_propb
            (owners : listArray uint256)
            (reqConfirms :  uint8)
            (mpk: uint256)
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

INT_1 {$$ LedgerDefault with Ledger_VMState := v2 $$}
       owners reqConfirms  ? .

(* OK *)
QuickCheck INT_1_propb.

Definition INT_2_propb
            (owners : listArray uint256)
            (reqConfirms :  uint8)
            (mpk: uint256)
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

INT_2 {$$ LedgerDefault with Ledger_VMState := v2 $$}
       owners reqConfirms  ? .

(* OK *)
QuickCheck INT_2_propb.

Definition INT_3_1_propb l
       (updateId :  uint64)
       (mpk: uint256)
       (acc: bool)
       (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

INT_3_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v2 $$})
       updateId  ? .

(* OK *)
QuickCheck INT_3_1_propb.

Definition INT_3_2_propb l
       (codeHash :  uint256) 
       (owners :  listArray uint256) 
       (reqConfirms :  uint8)
       (mpk: uint256)
       (acc: bool)
       (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

INT_3_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v2 $$})
       codeHash owners reqConfirms  ? .

(* OK *)
QuickCheck INT_3_2_propb.

Definition INT_3_3_propb l
       (transactionId :  uint64)
       (mpk: uint256)
       (acc: bool)
       (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

INT_3_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v2 $$})
       transactionId  ? .

(* OK *)
QuickCheck INT_3_3_propb.

Definition INT_3_4_propb l
       (dest :  address) 
       (value :  uint128) 
       (bounce :  boolean) 
       (allBalance :  boolean) 
       (payload :  cell_)
       (mpk: uint256)
       (acc: bool)
       (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

INT_3_4 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v2 $$})
       dest value bounce allBalance payload  ? .

(* OK *)
QuickCheck INT_3_4_propb.

Definition INT_3_5_propb l
            (dest :  address) 
            (value :  uint128)
            (bounce :  boolean)
            (flags :  uint16)
            (payload :  cell_) 
            (mpk: uint256)
            (acc: bool)
            (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

INT_3_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v2 $$})
       dest value bounce flags payload  ? .

(* OK *)
QuickCheck INT_3_5_propb.

Definition INT_5_propb
            (owners : listArray uint256)
            (reqConfirms :  uint8)
            (mpk: uint256)
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

INT_5 {$$ LedgerDefault with Ledger_VMState := v2 $$}
       owners reqConfirms  ? .

(* OK *)
QuickCheck INT_5_propb.

Definition INT_6_propb
            (owners : listArray uint256)
            (reqConfirms :  uint8)
            (mpk: uint256)
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

INT_6 {$$ LedgerDefault with Ledger_VMState := v2 $$}
       owners reqConfirms  ? .

(* OK *)
QuickCheck INT_6_propb.

Definition INT_7_1_propb
            (owners : listArray uint256)
            (reqConfirms :  uint8)
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

INT_7_1 {$$ LedgerDefault with Ledger_VMState := v2 $$}
       owners reqConfirms  ? .

(* OK *)
QuickCheck INT_7_1_propb.

Definition INT_7_2_propb
            (owners : listArray uint256)
            (reqConfirms :  uint8)
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

INT_7_2 {$$ LedgerDefault with Ledger_VMState := v2 $$}
       owners reqConfirms  ? .

(* FAILS -- probably ursus problem with while *)
QuickCheck INT_7_2_propb.
