Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String.
Require Import Setoid. 
Require Import ZArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Ascii.

Require Import FinProof.All.

Require Import UMLang.All. 
Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Require Import UrsusStdLib.Solidity.All.
Require Import UrsusStdLib.Solidity.unitsNotations.
Require Import UrsusTVM.Solidity.All.
Require Import UrsusTVM.Solidity.UrsusDefinitions.
Require Import UrsusTVM.Solidity.ReverseTranslatorConstructions.

Import UrsusNotations.
Local Open Scope xlist_scope.
Local Open Scope record.
Local Open Scope program_scope.
Local Open Scope glist_scope.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.

From elpi Require Import elpi.


Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Require Import multisig. 

Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Require Import FinProof.CommonInstances.

Require Import CommonQCEnvironment.
Require Import LocalState.

Notation rec := LocalStateLRecord.
Definition computed : LocalStateLRecord := Eval compute in default. 
#[global]
Instance def : XDefault LocalStateLRecord := {
  default := computed 
} . 
Definition VMStateDefault : VMStateLRecord  := Eval compute in default.
Definition LedgerDefault : LedgerLRecord LocalStateLRecord  := Eval compute in default. 

Definition incr_time (l: LedgerLRecord rec) (dt: N) :=
   let st := getPruvendoRecord Ledger_VMState l in 
   let t := getPruvendoRecord VMState_ι_now st in
   let newst := {$$ st with VMState_ι_now := Build_XUBInteger (uint2N t + dt) $$} in
   {$$ l with Ledger_VMState := newst $$}.

#[global, program]
Instance IDefault_booleq : XBoolEquable bool IDefault.
Next Obligation.
destruct H, H0.
refine true.
Defined.

(* TODO *)
Definition correctState (l: LedgerLRecord rec) := True.