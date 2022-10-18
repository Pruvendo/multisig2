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
Require Import CUE.Props.
Require Import CommonForProps.

Require Import  SetcodeMultisig. 

Definition CUE_1_propb l
        (updateId :  uint64) 
        (code : optional cell_)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in
CUE_1 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
        updateId code  ? .

(* OK *)
QuickCheck CUE_1_propb.

Definition CUE_2_propb l id
        (updateId :  uint64) 
        (code : optional cell_) 
        (custodianIndex :  uint8) 
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8)
        (lifetime : optional uint32)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CUE_2 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
        id updateId code custodianIndex codeHash owners reqConfirms lifetime ? .

(* fails SOMETIMES *)
QuickCheck CUE_2_propb.

Definition CUE_3_propb l id
        (updateId :  uint64)
        (code : optional cell_) 
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8)
        (lifetime : optional uint32)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CUE_3 (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
        id updateId code codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CUE_3_propb.


Definition CUE_4_propb l id
        (updateId :  uint64)
        (code : optional cell_) 
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8)
        (lifetime : optional uint32)
        (mpk: uint256)
        (acc: bool)
        (pk: uint256)
        timestamp
        now: bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_accepted := acc $$} in
let v2 := {$$ v1 with VMState_ι_msg_pubkey := pk $$} in
let v3 := {$$ v2 with VMState_ι_now := now $$} in
let v4 := {$$ v3 with VMState_ι_timestamp := timestamp $$} in

CUE_4  (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v4 $$})
        id updateId code codeHash owners reqConfirms lifetime ? .

(* OK *)
QuickCheck CUE_4_propb.


Definition CUE_6_2' l id id2 (updateId :  uint64)  (code : optional cell_) (codeHash : optional uint256) (owners : optional (listArray uint256)) (reqConfirms : optional uint8) (lifetime :  optional   uint32) : Prop := 
  let l' := exec_state (Uinterpreter (executeUpdate rec def updateId code)) l in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l) in
  let res := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  let ur := xMaybeMapDefault (fun x => x) (hmapLookup id m_updateRequests) dummyRequest  in
  let u2 := xMaybeMapDefault (fun x => x) (hmapLookup id2 res) dummyRequest  in
  let tr_id := getPruvendoRecord UpdateRequest_ι_id ur in 
  let tr_id2 := getPruvendoRecord UpdateRequest_ι_id u2 in 
  let pcode := (toValue (eval_state (sRReader || tvm->code() ) l)) in
  let ecode := (toValue (eval_state (sRReader || tvm->code() ) l')) in
  let ccode := (toValue (eval_state (sRReader || tvm->currentCode() ) l')) in
  let m_custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l') in
  let m_custodians_old := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let m_ownerKey_old := toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l) in
  let m_ownerKey := toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l') in
  let m_lifetime := toValue (eval_state (sRReader (m_lifetime_right rec def) ) l') in
  let m_lifetime_old := toValue (eval_state (sRReader (m_lifetime_right rec def) ) l) in
  let m_defaultRequiredConfirmations := toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l') in
  let m_defaultRequiredConfirmations_old := toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l) in
  let DEFAULT_LIFETIME := toValue (eval_state (sRReader (DEFAULT_LIFETIME_right rec def) ) l) in
  let m_requestsMask := toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l') in
  let m_updateRequestsMask := toValue (eval_state (sRReader (m_updateRequestsMask_right rec def) ) l') in
  let m_transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l') in
  let m_updateRequests := toValue (eval_state (sRReader (m_updateRequests_right rec def) ) l') in
  correctState l ->
  isError (eval_state (Uinterpreter (executeUpdate rec def updateId code)) l) = false -> 
  (* (u2 <> ur -> hmapIsMember id2 m_updateRequests -> hmapIsMember id2 res) ->
  length_ m_updateRequests - 1 = length_ res /\
  tr_id <> tr_id2 /\
  pcode = ecode /\
  ccode = ecode /\
  (xMaybeIsSome owners = true -> length_ (xMaybeMapDefault Datatypes.id owners default) <= length_ m_custodians ) /\
   checkMap1 m_custodians = true /\
  checkMap2 m_custodians (N.to_nat (length_ (xMaybeMapDefault Datatypes.id owners default))) (xMaybeMapDefault Datatypes.id owners default) = true /\
  (xMaybeIsSome owners = false -> m_custodians = m_custodians_old /\ m_ownerKey = m_ownerKey_old) /\
  xMaybeIsSome reqConfirms = true -> uint2N m_defaultRequiredConfirmations = N.min (length_ m_custodians) (uint2N (xMaybeMapDefault Datatypes.id reqConfirms default)) /\
  xMaybeIsSome reqConfirms = false -> m_defaultRequiredConfirmations = m_defaultRequiredConfirmations_old /\*)
  (xMaybeIsSome lifetime = false -> m_lifetime = m_lifetime_old) /\
  (xMaybeIsSome lifetime = true -> uint2N (xMaybeMapDefault Datatypes.id lifetime default) > 0 -> m_lifetime = (xMaybeMapDefault Datatypes.id lifetime default)) /\
  (xMaybeIsSome lifetime = true -> uint2N (xMaybeMapDefault Datatypes.id lifetime default) = 0 -> m_lifetime = DEFAULT_LIFETIME) (*/\
  i >= 0 -> i < 32 ->  N.land (uint2N m_updateRequestsMask) i = 0 /\
  m_transactions = default /\
  m_updateRequests = default /\
  i >= 0 -> i < 32 -> N.land (uint2N m_requestsMask) i = 0*).
  (* This makes qc freezes XD *)
  (* i >= 0 -> i < 32 -> N.shiftl (uint2N i) (uint2N m_updateRequestsMask) = 0. *)


Definition CUE_6_2_propb l id id2
        (updateId :  uint64)
        (code : optional cell_) 
        (codeHash : optional uint256) 
        (owners : optional (listArray uint256)) 
        (reqConfirms : optional uint8)
        (lifetime : optional uint32)
        (mpk: uint256)
        (acc: bool)
        (update: UpdateRequestLRecord)
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

let updates := getPruvendoRecord _m_updateRequests l in
let updates' := if hmapIsMember updateId updates then updates 
else xHMapInsert updateId update updates in


CUE_6_2'  (quickFixState {$$ 
        {$$ LedgerDefault with Ledger_MainState := 
        {$$ {$$ l with  _m_custodians := custodians' $$} 
                  with _m_updateRequests := updates' $$} $$}
                            with Ledger_VMState := v4 $$})
        id id2 updateId code codeHash owners reqConfirms lifetime ? .

(* Fail *)
QuickCheck CUE_6_2_propb.