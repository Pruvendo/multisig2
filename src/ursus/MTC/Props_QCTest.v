Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.
Require Import Coq.Program.Equality.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Require Import FinProof.All.

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
Require Import MTC.Props.
Require Import CommonForProps.

Require Import multisig.

(* TODO: add time to VMState and pass it as random argument to each propb*)
(* TODO: add time passing (advance now using incr_time function)*)
(* without time passing, expirations wouldn't be working correctly *)

Definition MTC_1_propb l
            (transactionId: uint64) 
            (mpk: uint256)
            (acc: bool)
            (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in

MTC_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$})
       transactionId  ? .

(* OK *)
QuickCheck MTC_1_propb.

Definition MTC_3_propb l
            (transactionId: uint64) 
            (mpk: uint256)
            (acc: bool)
            (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians : XHMap uint256 uint8 := getPruvendoRecord _m_custodians l in
let custodians' := if hmapIsMember mpk custodians then custodians 
else xHMapInsert mpk (Build_XUBInteger (length_ custodians)) custodians in

MTC_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians' $$}
        $$}with Ledger_VMState := v2 $$})
       transactionId  ? .

(* OK *)
QuickCheck MTC_3_propb.

Definition MTC_4_propb l
            (transactionId: uint64) 
            (mpk: uint256)
            (acc: bool)
            (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians : XHMap uint256 uint8 := getPruvendoRecord _m_custodians l in
let custodians' := if hmapIsMember mpk custodians then custodians 
else xHMapInsert mpk (Build_XUBInteger (length_ custodians)) custodians in

MTC_4 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians' $$}
        $$}with Ledger_VMState := v2 $$})
       transactionId  ? .

(* OK *)
QuickCheck MTC_4_propb.

Definition MTC_5_1_propb l
            (transactionId: uint64) 
            (mpk: uint256)
            (acc: bool)
            (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians : XHMap uint256 uint8 := getPruvendoRecord _m_custodians l in
let custodians' := if hmapIsMember mpk custodians then custodians 
else xHMapInsert mpk (Build_XUBInteger (length_ custodians)) custodians in

MTC_5_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians' $$}
        $$}with Ledger_VMState := v2 $$})
       transactionId  ? .

(* OK *)
QuickCheck MTC_5_1_propb.

Definition MTC_5_2_propb l
            (transactionId: uint64) 
            (mpk: uint256)
            (acc: bool)
            (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians : XHMap uint256 uint8 := getPruvendoRecord _m_custodians l in
let custodians' := if hmapIsMember mpk custodians then custodians 
else xHMapInsert mpk (Build_XUBInteger (length_ custodians)) custodians in

MTC_5_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians' $$}
        $$}with Ledger_VMState := v2 $$})
       transactionId  ? .

(* OK *)
QuickCheck MTC_5_2_propb.

(*Definition mpk := 0.
Definition custodians : mapping uint256 uint8 := CommonInstances.wrap CommonInstances.Map (Datatypes.cons
         (Build_XUBInteger mpk, (Build_XUBInteger 0)) Datatypes.nil).
Definition transactions : mapping uint64 MultisigWallet_ι_TransactionLRecord := CommonInstances.wrap CommonInstances.Map (Datatypes.cons
(Build_XUBInteger 0, default) Datatypes.nil).
Definition prog := confirmTransaction rec def (Build_XUBInteger 0).

Definition l := {$$ LedgerDefault with Ledger_MainState := 
        {$$ 
        {$$ default with  _m_custodians := custodians $$}
        with _m_transactions := transactions$$}
$$}.
Compute (isError (eval_state (Uinterpreter prog) l)).
Definition l' := Eval compute in exec_state (Uinterpreter prog) l.
*)

Definition MTC_6_propb l
            (transactionId: uint64) 
            (mpk: uint256)
            (acc: bool)
            (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in
let custodians : XHMap uint256 uint8 := getPruvendoRecord _m_custodians l in
let custodians' := if hmapIsMember mpk custodians then custodians 
else xHMapInsert mpk (Build_XUBInteger (length_ custodians)) custodians in

MTC_6 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
                {$$ l with  _m_custodians := custodians' $$}
        $$}with Ledger_VMState := v2 $$})
       transactionId  ? .

(* OK *)
QuickCheck MTC_6_propb.