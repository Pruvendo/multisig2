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

Definition MTC_1_propb l
            (transactionId: uint64) 
            (mpk: uint256)
            (acc: bool)
            (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_balance := Build_XUBInteger (10 * bal) $$} in

MTC_1 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$}
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

MTC_3 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v2 $$}
       transactionId  ? .

(* OK *)
QuickCheck MTC_3_propb.
