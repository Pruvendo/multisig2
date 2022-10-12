Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String.
Require Import Setoid. 
Require Import ZArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Ascii.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.
Require Import List.
Require Import FinProof.All.

Require Import UMLang.All. 
Require Import UrsusStdLib.Solidity.All.
Require Import UrsusStdLib.Solidity.unitsNotations.
Require Import UrsusTVM.Solidity.All.
Require Export UrsusContractCreator.UrsusDefinitions.
Require Export UrsusContractCreator.ReverseTranslatorConstructions.

Import UrsusNotations.
Local Open Scope xlist_scope.
Local Open Scope record.
Local Open Scope program_scope.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.

From elpi Require Import elpi.


From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Require Import multisig2. 

Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Require Import FinProof.CommonInstances.

Require Import CommonQCEnvironment.
Require Import LocalState.

#[global, program]
Instance listInfinite : listInfiniteFunRec_gen XList.
Next Obligation.
(* we have three while loops: *)
(* 1st -- max MAX_CUSTODIAN_COUNT + 1 = 33 iterations *)
(* 2nd -- max MAX_CLEANUP_TXNS + 1 = 41 iterations *)
(* 3rd -- ??? TODO investigate*)
exact (repeat PhantomPoint 41).
Defined.

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

Fixpoint Pos_bitcount (p: positive) :=
  match p with
    | xH => 1
    | xO p' => Pos_bitcount p'
    | xI p' => 1 + Pos_bitcount p'
  end.

Definition N_bitcount (n: N) :=
  match n with 
    | N0 => 0
    | Npos p => Pos_bitcount p
  end.

Definition computeCorrectSignsReceived (tx : TransactionLRecord) :=
  let confirmationsMask := getPruvendoRecord Transaction_ι_confirmationsMask tx in
  N_bitcount (uint2N confirmationsMask).

Definition transactionsCorrect (txs: Datatypes.list (uint64 * TransactionLRecord))  :=
  List.forallb (fun tx : (uint64 * _) => (
  andb
    (Common.eqb (fst tx) (getPruvendoRecord Transaction_ι_id (snd tx))))
    (Common.eqb (computeCorrectSignsReceived (snd tx)) 
      (uint2N (getPruvendoRecord Transaction_ι_signsReceived (snd tx))))
  ) txs.

Definition noDuplicates (txs: Datatypes.list (uint64 * TransactionLRecord)) :=
  List.forallb (fun tx => Common.eqb (length_ (List.filter
    (fun tx' => Common.eqb tx tx') txs)) 1) txs.

Definition get_index (tx : TransactionLRecord) : N := 
  uint2N (TransactionLGetField Transaction_ι_index tx).

Definition noDuplicateIds (txs: Datatypes.list (uint64 * TransactionLRecord)) :=
  List.forallb (fun tx => Common.eqb (length_ (List.filter
    (fun tx' => Common.eqb (get_index (snd tx)) (get_index (snd tx'))) txs)) 1) txs.

Definition computeCorrectRequestMask (transactions: mapping uint64 TransactionLRecord) :=
  List.fold_left (fun acc e => 
    acc + (N.shiftl 1 (8 * (get_index (snd e))))
  ) (unwrap transactions) 0.

Definition requestMaskCorrect (requestMask: uint256) (transactions: mapping uint64 TransactionLRecord) :=
  Common.eqb (uint2N requestMask) (computeCorrectRequestMask transactions).

Definition correctState l := 
    let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
    let custodianCount := toValue (eval_state (sRReader (m_custodianCount_right rec def) ) l) in
    let ownerKey := toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l) in
    let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
    let requestMask := toValue (eval_state (sRReader (m_requestsMask_right rec def) ) l) in
    length_ custodians = uint2N custodianCount /\
    hmapIsMember ownerKey custodians = true /\
    transactionsCorrect (unwrap transactions) = true /\
    noDuplicates (unwrap transactions) = true /\
    noDuplicateIds (unwrap transactions) = true /\
    requestMaskCorrect requestMask transactions = true
    .

Import ListNotations.
Definition get_id (tx : TransactionLRecord) : N := 
  uint2N (TransactionLGetField Transaction_ι_id tx).
Fixpoint dedupTransactions (txs: Datatypes.list (uint64 * TransactionLRecord))  (mem: mapping N bool) := 
  match txs with 
  | [ ]%list => [ ]%list
  | (tx :: txs)%list => 
  let id := get_id (snd tx) in
  if hmapIsMember id mem then dedupTransactions txs mem
  else let mem' := xHMapInsert id true mem in
  (tx :: dedupTransactions txs mem')%list
  end.

 Definition quickFixState (l: LedgerLRecord rec) : LedgerLRecord rec :=
  let custodians := toValue (eval_state (sRReader (m_custodians_right rec def) ) l) in
  let ownerKey := toValue (eval_state (sRReader (m_ownerKey_right rec def) ) l) in
  let custodians' := if hmapIsMember ownerKey custodians then custodians 
    else xHMapInsert ownerKey (Build_XUBInteger (length_ custodians)) custodians in
  let defaultRequired := toValue (eval_state (sRReader (m_defaultRequiredConfirmations_right rec def) ) l) in
  let transactions := toValue (eval_state (sRReader (m_transactions_right rec def) ) l) in
  let transactions':= (CommonInstances.wrap Map (dedupTransactions (map 
    (fun tx : (uint64 * TransactionLRecord) => (fst tx, 
      {$$ {$$ snd tx with Transaction_ι_id := fst tx $$}
         with Transaction_ι_signsReceived := (Build_XUBInteger (computeCorrectSignsReceived (snd tx)))
      $$} : TransactionLRecord))
  (unwrap transactions)) (CommonInstances.wrap Map Datatypes.nil))) in
  {$$ l with Ledger_MainState := 
    {$$ {$$ {$$ {$$getPruvendoRecord Ledger_MainState l with 
      _m_custodianCount := Build_XUBInteger (length_ custodians')
    $$} with
      _m_custodians := custodians' 
    $$}
     with
      _m_transactions := transactions'
    $$}
     with
      _m_requestsMask := (Build_XUBInteger (computeCorrectRequestMask transactions'))
    $$}
  $$}. 

#[global]
Instance xhmap_booleq {K V} `{XBoolEquable bool K} `{XBoolEquable bool V}: XBoolEquable bool (XHMap K V).
Proof.
  esplit. intros. apply ( @XBoolEquableList(K*V)).
  apply pair_xbool_equable.
  exact (unwrap X). exact (unwrap X0).
Defined.

#[global]
Instance xarray_booleq {K} `{XBoolEquable bool K}: XBoolEquable bool (listArray K).
Proof.
  esplit. intros. apply ( @XBoolEquableList(K)). auto.
  exact (unwrap X). exact (unwrap X0).
Defined.

#[global]
Instance xqueue_booleq {K} `{XBoolEquable bool K}: XBoolEquable bool (XQueue K).
Proof.
  esplit. intros. apply ( @XBoolEquableList(XUInteger*K)). 
  apply pair_xbool_equable.
  exact (unwrap X). exact (unwrap X0).
Defined.

Definition T := Eval compute in LedgerLRecord rec.
Definition ledgerEqb : T -> T -> bool := Common.eqb.