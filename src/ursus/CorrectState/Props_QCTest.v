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
Require Import LocalState.
Require Import CorrectState.Props.
Require Import CommonForProps.

Require Import multisig.

Definition CS_0_propb
            (owners : listArray uint256)
            (reqConfirms :  uint8)
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CS_0 {$$ LedgerDefault with Ledger_VMState := v2 $$}
       owners reqConfirms  ? .

(* FAILS -- probably ursus problem with while *)
QuickCheck CS_0_propb.

Definition CS_1_propb
              (updateId :  uint64)
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CS_1 {$$ LedgerDefault with Ledger_VMState := v2 $$}
       updateId  ? .

(* OK *)
QuickCheck CS_1_propb.

Definition CS_2_propb
              (codeHash :  uint256) 
              (owners :  listArray uint256) 
              (reqConfirms :  uint8)
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CS_2 {$$ LedgerDefault with Ledger_VMState := v2 $$}
codeHash owners reqConfirms ? .

(* OK *)
QuickCheck CS_2_propb.

Definition CS_3_propb
            (transactionId :  uint64) 
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CS_3 {$$ LedgerDefault with Ledger_VMState := v2 $$}
       transactionId ? .

(* OK *)
QuickCheck CS_3_propb.

Definition CS_4_propb
       (dest :  address) 
       (value :  uint128) 
       (bounce :  boolean) 
       (allBalance :  boolean) 
       (payload :  cell_) 
            (acc: bool)
            (pk: uint256): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := pk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in

CS_4 {$$ LedgerDefault with Ledger_VMState := v2 $$}
       dest value bounce allBalance payload ? .

(* OK *)
QuickCheck CS_4_propb.

Definition CS_5_propb l
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

CS_5 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v2 $$})
       dest value bounce flags payload  ? .

(* OK *)
QuickCheck CS_5_propb.

Definition CS_6_propb l
            (updateId :  uint64) 
            (code :  TvmCell)
            (mpk: uint256)
            (acc: bool)
            (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians := CommonInstances.wrap Map (Datatypes.cons (mpk, Build_XUBInteger 0) Datatypes.nil) in

CS_6 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians $$}
         $$}with Ledger_VMState := v2 $$})
         updateId code  ? .

(* OK *)
QuickCheck CS_6_propb.


Definition VMStateDefault : VMStateLRecord  := Eval compute in default.
Definition LedgerDefault : LedgerLRecord LocalStateLRecord  := Eval compute in default. 

Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Local Open Scope list_scope.
Definition l : LedgerLRecord rec := xpair 0 (xpair 0 (xpair 0 (xpair 0 (xpair nil (xpair nil (xpair 0 (xpair [(0,(0,(0,(0,(0,(0,(0,([0],0))))))))] (xpair 0 (xpair 0 0))))))))).
Variables (updateId : uint64) (code : TvmCell).
Definition ev := Eval compute in eval_state (Uinterpreter (executeUpdate rec def updateId code)) l.
Definition l' := Eval compute in exec_state (Uinterpreter (executeUpdate rec def updateId code)) l.
Compute toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l'). 
Compute (isError ev).