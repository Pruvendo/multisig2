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
Require Import SetcodeMultisig_LocalState. 
Require Import CorrectState.Props.
Require Import CommonForProps.

Require Import  SetcodeMultisig. 

Definition CS_1_propb l
              (updateId :  uint64)
            (acc: bool)
            (pk: uint256)
            timestamp
            (now:N) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CS_1 (quickFixState {$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v4 $$})
       updateId  ? .

(* OK *)
QuickCheck CS_1_propb.

Definition CS_0_propb
       (owners : listArray uint256)
       (reqConfirms :  uint8)
       (lifetime :  uint32)
       (acc: bool)
       (pk: uint256)
       timestamp
       (now : N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (4000 + now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CS_0 {$$ LedgerDefault with Ledger_VMState := v4 $$}
       owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CS_0_propb.

Definition CS_2_propb l
       (codeHash : optional uint256) 
       (owners : optional (listArray uint256)) 
       (reqConfirms : optional uint8)
       (lifetime : optional uint32)
       (acc: bool)
       (pk: uint256)
       timestamp
       (now:N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CS_2 (quickFixState {$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v4 $$})
       codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CS_2_propb.

Definition CS_3_propb l
            (transactionId :  uint64) 
            (acc: bool)
            (pk: uint256)
            timestamp
            (now:N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CS_3 (quickFixState {$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v4 $$})
       transactionId ? .

(* OK *)
QuickCheck CS_3_propb.

Definition CS_4_propb l
       (dest :  address) 
       (value :  uint128) 
       (bounce :  boolean) 
       (allBalance :  boolean) 
       (payload :  cell_)
       (stateInit :  optional TvmCell) 
       (acc: bool)
       (pk: uint256)
       timestamp
       (now:N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CS_4 (quickFixState {$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v4 $$})
       dest value bounce allBalance payload stateInit ? .

(* OK *)
QuickCheck CS_4_propb.

Definition CS_5_propb l
            (dest :  address) 
            (value :  uint128)
            (bounce :  boolean)
            (flags :  uint8)
            (payload :  cell_) 
            (mpk: uint256)
            (acc: bool)
            (bal: N)
            timestamp
            (now:N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

CS_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v4 $$})
       dest value bounce flags payload  ? .

(* OK *)
QuickCheck CS_5_propb.

Definition CS_6_propb l
            (updateId :  uint64) 
            (code : optional TvmCell)
            (mpk: uint256)
            (acc: bool)
            (bal: N)
            timestamp
            (now:N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in
let v3 := {$$ v2 with VMState_ι_now := Build_XUBInteger (now) $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CS_6 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v4 $$})
         updateId code  ? .

(* OK *)
QuickCheck CS_6_propb.