Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.
Require Import Coq.Program.Equality.
Require Import Logic.FunctionalExtensionality.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Require Import FinProof.Common. 
Require Import FinProof.Lib.BoolEq.
Require Import FinProof.MonadTransformers21.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.Types.IsoTypes.

Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Solidity.stdTypes.

Require Import UrsusTVM.Solidity.tvmTypes.
Require Import UrsusTVM.Solidity.tvmFunc.
Require Import UrsusTVM.Solidity.tvmNotations.
Require Import UrsusTVM.Solidity.tvmCells.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

(*string*)

Derive Show for ascii.
Derive Shrink for ascii.
Derive GenSized for ascii.

Derive Show for String.string.
Derive Shrink for String.string.
Derive GenSized for String.string.

Derive Show for unit.
Derive Shrink for unit.
Derive GenSized for unit.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Notation " x 'deciever' " := ( N.mul x 1 ) (at level 100).

Derive Show for xprod.
Derive Shrink for xprod.
Derive GenSized for xprod.

Derive Show for prod.
Derive Shrink for prod.
Derive GenSized for prod.

(* Derive Show for option.
Derive Shrink for option.
Derive GenSized for option. *)

(*isotypes*)

#[local]
Instance iso_show : forall X Y`{IsoTypes X Y}`{Show Y},  Show X.
intros.
split.
intros.
refine (show (x2y X0)).
Defined.

#[local]
Instance iso_shrink : forall X Y`{IsoTypes X Y}`{Shrink Y}, Shrink X.
intros.
split.
intros.
pose proof (shrink (x2y X0)).
refine (List.map y2x X1).
Defined.

#[local]
Instance iso_genSized : forall X Y`{IsoTypes X Y}`{GenSized Y}, GenSized X.
intros.
split.
intros.
pose proof (arbitrarySized H1 : G Y).
refine (fmap y2x X0).
Defined.

#[local]
Remove Hints iso_show : typeclass_instances.
#[local]
Remove Hints iso_shrink : typeclass_instances.
#[local]
Remove Hints iso_genSized : typeclass_instances.

(* sum *)

Open Scope string_scope.

#[global]
Instance sum_show : forall X Y`{Show X }`{Show Y}, Show (X + Y).
intros.
split.
intros.
destruct X0.
refine ( "left: " ++ (show x)).
refine ( "right: " ++ (show y)).
Defined.

#[global]
Instance sum_shrink : forall X Y`{Shrink X}`{Shrink Y}, Shrink (X+Y).
intros.
split.
intros.
destruct X0.
pose proof (shrink x).
refine (List.map inl X0).
pose proof (shrink y).
refine (List.map inr X0).
Defined.

#[global]
Instance sum_genSized : forall X Y`{GenSized X}`{GenSized Y}, GenSized (X+Y).
intros.
split.
intros.
pose proof (arbitrarySized H1: G bool).
Search (forall X Y, G X -> (X -> G Y) -> G Y).
eapply bindGen. { exact X0. }
intros b. destruct b. 
-
pose proof (arbitrarySized H1: G X).
refine (fmap inl X1).
-
pose proof (arbitrarySized H1: G Y).
refine (fmap inr X1).
Defined.

(*uint*)

Definition uint_n_to_uint {n} (x: XUBInteger n) : XUInteger.
dependent destruction x.
exact x.
Defined.

#[global]
Instance iso_uint: forall n, IsoTypes (XUBInteger n) (XUInteger).
intros.
esplit with (x2y := fun x => uint_n_to_uint x ) (y2x := Build_XUBInteger); try reflexivity.
extensionality x.
unfold compose.
dependent destruction x.
reflexivity.
Defined.

#[global]
Instance iso_option: forall X, IsoTypes (option X) (unit + X).
intros.
esplit with (x2y := fun x => match x with
                             | Some x => inr x
                             | None => inl tt end  ) (y2x := fun y =>  match y with
                                                             | inr x => Some x
                                                             | inl tt => None end); try reflexivity.
extensionality x. unfold compose.
destruct x; try destruct u; reflexivity.
extensionality y. unfold compose.
destruct y; reflexivity.
Defined.

#[global]
Instance option_gensized: forall X`{GenSized X}, GenSized (option X).
intros.
eapply iso_genSized.
eapply iso_option.
eapply sum_genSized.
apply GenSizedunit.
apply H.
Defined.


#[global]
Instance uint_n_show: forall n, Show (XUBInteger n) .
intros.
eapply iso_show.
eapply iso_uint.
apply showN.
Defined.

#[global]
Instance uint_n_shrink: forall n, Shrink (XUBInteger n) .
intros.
eapply iso_shrink.
eapply iso_uint.
apply shrinkN.
Defined.

#[global]
Instance uint_n_genSized: forall n, GenSized (XUBInteger n) .
intros.
eapply iso_genSized.
eapply iso_uint.
apply genNSized.
Defined.

(* mappings *)

#[global]
Instance xhmap_show : forall K V `{Show K} `{Show V}, Show (XHMap K V) :=
{
  show m := show (unwrap m)
}.

#[global]
Instance xhmap_shrink : forall K V `{Shrink K} `{Shrink V}, Shrink (XHMap K V) :=
{
  shrink m := List.map (CommonInstances.wrap Map) (shrink (unwrap m))
}.

#[global]
Instance xhmap_gensized : forall K V `{GenSized K} `{GenSized V}, GenSized (XHMap K V) :=
{
  arbitrarySized n := fmap (CommonInstances.wrap Map) (arbitrarySized n)
}.

(* queues *)

#[global]
Instance xqueue_show : forall V `{Show V}, Show (XQueue V) :=
{
  show m := show (unwrap m)
}.

#[global]
Instance xqueue_shrink : forall V `{Shrink V}, Shrink (XQueue V) :=
{
  shrink m := List.map (CommonInstances.wrap Queue) (shrink (unwrap m))
}.

#[global]
Instance xqueue_gensized : forall V `{GenSized V}, GenSized (XQueue V) :=
{
  arbitrarySized n := fmap (CommonInstances.wrap Queue) (arbitrarySized n)
}.

(* arrays *)
#[global]
Instance xarray_show : forall V `{Show V}, Show (listArray V) :=
{
  show m := show (unwrap m)
}.

#[global]
Instance xarray_shrink : forall V `{Shrink V}, Shrink (listArray V) :=
{
  shrink m := List.map (CommonInstances.wrap Array) (shrink (unwrap m))
}.

#[global]
Instance xarray_gensized : forall V `{GenSized V}, GenSized (listArray V) :=
{
  arbitrarySized n := fmap (CommonInstances.wrap Array) (arbitrarySized n)
}.


(*messages*)

Definition fromMessage {I} (m: OutgoingMessage I): (unit*InternalMessageParamsLRecord)+(I*InternalMessageParamsLRecord).
destruct m.
refine (inl (tt,i)).
refine (inr (i0,i)).
Defined.

Definition toMessage {I} (m: (unit*InternalMessageParamsLRecord)+(I*InternalMessageParamsLRecord)) : OutgoingMessage I.
destruct m. destruct p.
refine (EmptyMessage _ i).
destruct p.
refine (OutgoingInternalMessage i0 i).
Defined.

#[global]
Instance iso_OutgoingMessage: forall I , IsoTypes (OutgoingMessage I) ((unit*InternalMessageParamsLRecord)+I*InternalMessageParamsLRecord).
intros.
esplit with (x2y := fromMessage )
            (y2x := toMessage); try reflexivity.
all: unfold compose.            
extensionality m.
destruct m.
simpl. destruct p. simpl. destruct u. reflexivity.
simpl. destruct p. reflexivity.
extensionality m.
destruct m.
simpl. reflexivity.
simpl. reflexivity.
Defined.

(*cells*)

Search TvmCellLike.
#[global]
Instance iso_cell: forall n , IsoTypes (TvmCellLike n) Precell.
intros.
esplit with (x2y := get_cell_repr_ )
            (y2x := CellLike  _); try reflexivity.
extensionality x.             
destruct x; reflexivity.
Defined.


#[global]
Instance ShowCellPackedValue: Show CellPackedValue := {
  show v := match v with
  | CPBool b => show b ++  " : bool"
  | CPNat n => show n ++ " : coq_nat"
  | CPXInteger i => show i ++ " : int"
  | CPString s => show s ++ " : string"
  | CPXUBInteger n m => show m ++ " : uint" ++ show n
  end
}.

#[global]
Instance ShowCellSizedValue: Show CellSizedValue := {
  show v := match v with
  | CellSizedV n v => show v ++ " [size " ++ show n ++ "]"
  end
}.

#[global]
Instance ShowPrecell: Show Precell.
exists. intros [c _].
refine (let repeatString s := fix F n := match n with
        | O => ""
        | S n' => s ++ F n'
        end in _).
refine (let joinStrings sep := fix F ss := match ss with
        | nil => ""
        | s::nil => s
        | s::ss => s ++ sep ++ F ss
        end in _).
refine (let indentEach ls := 
          map (fun s => "->" ++ s) ls in _).
refine (let showLines c := _ in joinStrings nl (showLines c)).
refine ("" :: ((fix F (c : PrecellTree) := _) c)).
refine (
match c with
| Build_PrecellTree vs Null Null Null Null => _
| Build_PrecellTree vs (Ref r1) Null Null Null => _
| Build_PrecellTree vs (Ref r1) (Ref r2) Null Null => _
| Build_PrecellTree vs (Ref r1) (Ref r2) (Ref r3) Null => _
| Build_PrecellTree vs (Ref r1) (Ref r2) (Ref r3) (Ref r4) => _
| _ => nil
end).
all: refine (show vs :: indentEach _).
{ refine nil. }
{ refine (F r1). }
{ refine (cat (F r1) (F r2)). }
{ refine (cat (F r1) (cat (F r2) (F r3))). }
{ refine (cat (F r1) (cat (F r2) (cat (F r3) (F r4)))). }
Defined.

#[global]
Instance ShrinkPrecell: Shrink Precell.
exists. intros c.
refine nil.
Defined.

#[global]
Instance GenSizedPrecell: GenSized Precell.
exists.
refine (fun _ => elems [EmptyPrecell]).
Defined.

(*cell_*)

#[global]
Instance cell_show: Show cell_.
eapply iso_show.
eapply iso_cell.
apply ShowPrecell.
Defined.

#[global]
Instance cell_shrink: Shrink cell_.
eapply iso_shrink.
eapply iso_cell.
apply ShrinkPrecell.
Defined.

#[global]
Instance cell_genSized: GenSized cell_.
eapply iso_genSized.
eapply iso_cell.
apply GenSizedPrecell.
Defined.

(*builder_*)

#[global]
Instance builder_show: Show builder_.
eapply iso_show.
eapply iso_cell.
apply ShowPrecell.
Defined.

#[global]
Instance builder_shrink: Shrink builder_.
eapply iso_shrink.
eapply iso_cell.
apply ShrinkPrecell.
Defined.

#[global]
Instance builder_genSized: GenSized builder_.
eapply iso_genSized.
eapply iso_cell.
apply GenSizedPrecell.
Defined.

(*outgoing message*)

#[global]
Instance OutgoingMessage_show: forall I`{Show I}, Show (OutgoingMessage I).
intros.
eapply iso_show.
eapply iso_OutgoingMessage.
eapply sum_show.
eapply Showprod.
eapply Showprod.
Defined.

#[global]
Instance OutgoingMessage_shrink: forall I`{Shrink I}, Shrink (OutgoingMessage I).
intros.
eapply iso_shrink.
eapply iso_OutgoingMessage.
eapply sum_shrink.
eapply Shrinkprod.
eapply Shrinkprod.
Defined.

#[global]
Instance OutgoingMessage_genSized: forall I`{GenSized I}, GenSized (OutgoingMessage I).
intros.
eapply iso_genSized.
eapply iso_OutgoingMessage.
eapply sum_genSized.
eapply GenSizedprod.
eapply GenSizedprod.
Defined.

(* Print Instances GenSized. *)


(*interfaces*)

Require Import multisig2.
(* TODO *)
(* Derive Show for Itmp. *)
(* Derive Shrink for Itmp. *)
(* Derive GenSized for Itmp. *)

(*PhantomType*)

#[global]
Instance iso_phantom: IsoTypes PhantomType unit.
esplit with (x2y:=fun  _ => tt) (y2x:=fun _ => PhantomPoint).
extensionality x.
unfold compose.
destruct x. reflexivity.
extensionality x.
unfold compose.
apply phantom_all.
Defined.

#[global]
Instance phantom_show: Show PhantomType .
eapply iso_show.
apply iso_phantom.
apply Showunit.
Defined.

#[global]
Instance phantom_shrink: Shrink PhantomType .
eapply iso_shrink.
apply iso_phantom.
apply Shrinkunit.
Defined.

#[global]
Instance phantom_genSized: GenSized PhantomType .
eapply iso_genSized.
apply iso_phantom.
apply GenSizedunit.
Defined.

(*MessagesAndEvents*)

#[local]
Remove Hints isoid : typeclass_instances. 
#[local]
Remove Hints iso_show : typeclass_instances.
#[local]
Remove Hints iso_shrink : typeclass_instances.
#[local]
Remove Hints iso_genSized : typeclass_instances.

(*VMState*)

#[global] 
Instance VMState_Show: Show VMStateLRecord.
refine Showxprod.
Defined.

#[global] 
Instance VMState_Shrink: Shrink VMStateLRecord.
refine Shrinkxprod.
Defined.

#[global] 
Instance VMState_GenSized: GenSized VMStateLRecord. 
refine GenSizedxprod.
Defined.

Definition implb (a b: bool) := orb (negb a) b.

Definition bimplb (a b: bool) := andb  (implb a b)  (implb b a).

#[global]
Instance true_dec: Dec True.
esplit.
unfold decidable.
left. auto.
Defined.

#[global]
Instance ge_dec: forall m n, Dec (N.ge m n).
intros.
esplit.
unfold decidable.
remember (N.ltb m n).
destruct b.
symmetry in Heqb.
apply N.ltb_lt in Heqb.
right. lia.
symmetry in Heqb.
apply N.ltb_ge in Heqb.
left. lia.
Defined.

#[global]
Instance lt_dec: forall m n, Dec (N.lt m n).
intros.
esplit.
unfold decidable.
remember (N.ltb m n).
destruct b.
symmetry in Heqb.
apply N.ltb_lt in Heqb.
left. lia.
symmetry in Heqb.
apply N.ltb_ge in Heqb.
right. lia.
Defined.

#[global]
Instance le_dec: forall m n, Dec (N.le m n).
intros.
esplit.
unfold decidable.
remember (N.leb m n).
destruct b.
symmetry in Heqb.
apply N.leb_le in Heqb.
left. lia.
symmetry in Heqb.
apply N.leb_gt in Heqb.
right. lia.
Defined.

#[global]
Instance gt_dec: forall m n, Dec (N.gt m n).
intros.
esplit.
unfold decidable.
remember (N.leb m n).
destruct b.
symmetry in Heqb.
apply N.leb_le in Heqb.
right. lia.
symmetry in Heqb.
apply N.leb_gt in Heqb.
left. lia.
Defined.

#[global]
Instance Dec_equiv : forall {P Q : Prop}, Dec P -> Dec Q -> Dec (P <-> Q) .
intros.
eapply Dec_conj.
Defined.

Definition uint2N {n} (x: XUBInteger n) : N.
dependent destruction x.
refine x.
Defined.

#[global] Instance prod_Dec: forall X Y (x1 x2: X) (y1 y2: Y) `{Dec (x1=x2)}`{Dec (y1=y2)}, Dec (pair x1 y1 = pair x2 y2).
intros.
esplit.
unfold decidable.
destruct H, H0.
destruct dec, dec0.
left.
congruence.
right.
unfold not.
intros.
inversion H.
contradiction.
right.
unfold not.
intros.
inversion H.
contradiction.
right.
unfold not.
intros.
inversion H.
contradiction.
Defined.

#[global] Instance xprod_Dec: forall X Y (x1 x2: X) (y1 y2: Y) `{Dec (x1=x2)}`{Dec (y1=y2)}, Dec (xpair x1 y1 = xpair x2 y2).
intros.
esplit.
unfold decidable.
destruct H, H0.
destruct dec, dec0.
left.
congruence.
right.
unfold not.
intros.
inversion H.
contradiction.
right.
unfold not.
intros.
inversion H.
contradiction.
right.
unfold not.
intros.
inversion H.
contradiction.
Defined.

#[global]
Instance XUBIntegerEq_Dec {n} (a b: XUBInteger n): Dec (a = b).
destruct a,b.
esplit.
unfold decidable.
decide equality.
decide equality.
decide equality.
Defined.

#[global]
Instance addressEq_Dec (a b: address): Dec (a = b).
destruct a,b.
esplit.
unfold decidable.
eapply prod_Dec.
esplit.
unfold decidable.
decide equality.
decide equality.
decide equality.
esplit.
unfold decidable.
decide equality.
decide equality.
decide equality.
Defined.

#[global]
Instance precell_Dec (a b: Precell): Dec (a = b).
esplit.
unfold decidable.
destruct (Common.eqb a b) eqn:Heqb.
{ left. now apply eqb_spec_intro. }
right. intros Heq. apply eqb_spec_intro in Heq. congruence.
Defined.

#[global]
Instance cellEq_Dec (a b: cell_): Dec (a = b).
esplit.
unfold decidable.
decide equality.
apply precell_Dec.
Defined.

#[global]
Instance cellBoolEq: XBoolEquable bool cell_ .
esplit.
intros.
pose proof (cellEq_Dec H H0).
destruct H1.
destruct dec.
refine true.
refine false.
Defined.



#[global]
Instance optionEq_Dec {X}`{forall (a b:X),Dec (a=b) } (a b: option X): Dec (a = b).
esplit.
unfold decidable.
decide equality.
eapply H.
Defined.



#[global] Instance VMStateEq_Dec: forall (l1 l2: VMStateLRecord), Dec (l1 = l2).
intros.
esplit.
unfold decidable.
repeat decide equality.
all: apply precell_Dec.
Defined.



Require Import FinProof.Common.
Require Import FinProof.CommonInstances.

(* TODO: booleq for interfaces *)
(*
#[global]
Instance IKWFundParticipant_booleq : XBoolEquable bool 
         Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant.
esplit.
refine (fun x y =>
    match x, y with
    | IKWFundParticipant.Interface.IonVoteReject x1           ,
      IKWFundParticipant.Interface.IonVoteReject y1             => eqb x1 y1
    | IKWFundParticipant.Interface.IonVoteAccept              ,
      IKWFundParticipant.Interface.IonVoteAccept                => true
    | IKWFundParticipant.Interface.IacknowledgeFunds          ,
      IKWFundParticipant.Interface.IacknowledgeFunds            => true
    | IKWFundParticipant.Interface.IsendFunds c1              ,
      IKWFundParticipant.Interface.IsendFunds d1                => eqb c1 d1
    | IKWFundParticipant.Interface.Iinitialize x1 x2 x3 x4 x5 ,
      IKWFundParticipant.Interface.Iinitialize y1 y2 y3 y4 y5   => 
        eqb x1 y1 && eqb x2 y2 && eqb x3 y3 && eqb x4 y4 && eqb x5 y5
    | IKWFundParticipant.Interface.InotifyParticipant x1 x2 x3,
      IKWFundParticipant.Interface.InotifyParticipant y1 y2 y3  =>
        eqb x1 y1 && eqb x2 y2 && eqb x3 y3
    | _, _                         => false
    end).
Defined.



#[global]
Instance IBlank_booleq : XBoolEquable bool 
         Interfaces.IBlank.IBlank.Interface.IBlank.
esplit.
refine (fun x y => match x, y with
| IBlank.Interface.Ivote x1 x2 x3 x4 x5 x6          ,
IBlank.Interface.Ivote y1 y2 y3 y4 y5 y6            => 
    eqb x1 y1 && eqb x2 y2 && eqb x3 y3 && eqb x4 y4 && eqb x5 y5 && eqb x6 y6
| IBlank.Interface.IacknowledgeDeploy a1 x1          ,
  IBlank.Interface.IacknowledgeDeploy b1 y1            => eqb a1 b1 && eqb x1 y1
| IBlank.Interface.IacknowledgeFinalizeRight a1 x1 x2,
  IBlank.Interface.IacknowledgeFinalizeRight b1 y1 y2  => eqb a1 b1 && eqb x1 y1 && eqb x2 y2
| IBlank.Interface.IacknowledgeFinalizeLeft x1 x2    ,
  IBlank.Interface.IacknowledgeFinalizeLeft y1 y2      => eqb x1 y1 && eqb x2 y2
| IBlank.Interface.IisFundReady x1 x2                , 
  IBlank.Interface.IisFundReady y1 y2                  => eqb x1 y1 && eqb x2 y2
| IBlank.Interface.InotifyRight a1 x1 x2 x3          ,
  IBlank.Interface.InotifyRight b1 y1 y2 y3            => 
    eqb a1 b1 && eqb x1 y1 && eqb x2 y2 && eqb x3 y3
| IBlank.Interface.InotifyLeft x1 x2 x3 x4           ,
  IBlank.Interface.InotifyLeft y1 y2 y3 y4             =>
    eqb x1 y1 && eqb x2 y2 && eqb x3 y3 && eqb x4 y4
| _, _                                => false
end).
Defined.
 
#[global]
Instance IKWFund_booleq : XBoolEquable bool 
         Interfaces.IKWFund.IKWFund.Interface.IKWFund.
esplit.
refine (fun x y => match x, y with
  | IsendKWDPoolParams x1 x2 c1  ,
    IsendKWDPoolParams y1 y2 d1    => eqb x1 y1 && eqb x2 y2 && eqb c1 d1
  | IsendFromGiverParams a1 x1 c1,
    IsendFromGiverParams b1 y1 d1  => eqb a1 b1 && eqb x1 y1 && eqb c1 d1
  | _, _                           => false
  end).
Defined.


#[global]
Instance IDFromGiver_booleq : XBoolEquable bool 
         FromGiver.DFromGiver.Interface.IDFromGiver.
esplit.
refine (fun x y =>
    match x, y with
    | IonVoteReject x1           ,
      IonVoteReject y1             => eqb x1 y1
    | IonVoteAccept              ,
      IonVoteAccept                => true
    | IacknowledgeFunds          ,
      IacknowledgeFunds            => true
    | IsendFunds c1              ,
      IsendFunds d1                => eqb c1 d1
    | Iinitialize x1 x2 x3 x4 x5 ,
      Iinitialize y1 y2 y3 y4 y5   => 
        eqb x1 y1 && eqb x2 y2 && eqb x3 y3 && eqb x4 y4 && eqb x5 y5
    | InotifyParticipant x1 x2 x3,
      InotifyParticipant y1 y2 y3  =>
        eqb x1 y1 && eqb x2 y2 && eqb x3 y3
    | DFromGiver.Interface.IreturnFunds,
      DFromGiver.Interface.IreturnFunds => true
    | DFromGiver.Interface.Ireceive,
      DFromGiver.Interface.Ireceive => true
    | DFromGiver.Interface._Iconstructor x1 x2,
      DFromGiver.Interface._Iconstructor y1 y2 => eqb x1 y1 && eqb x2 y2
    | _, _                         => false
    end).
Defined.
*)
#[global]
Instance OutgoingMessage_booleq: forall I `{XBoolEquable bool I}, XBoolEquable bool 
         (OutgoingMessage I).
intros.
esplit.
intros.
case_eq X; intros; case_eq X0; intros.
refine (eqb i i0). refine false. refine false.
refine  (eqb i i1 && eqb i0 i2).
Defined.


Definition isMessageSent {I}`{XBoolEquable bool I} (m: OutgoingMessage I) (a: address) (n: N)
                         (l: XHMap address (XQueue (OutgoingMessage I))) : bool :=
  let subm := q2m (hmapFindWithDefault default a l) in                      
  let maxk : option N := xHMapMaxKey subm in
  match maxk with 
    | None => false
    | Some k => 
        match hmapLookup (k-n) subm with
        | None => false
        | Some m' => eqb m m'
        end
  end. 

Import ListNotations.

Definition isOnlyMessage {I} (l: XHMap address (XQueue (OutgoingMessage I))) : bool :=
  match unwrap l with 
  | [(a, subm)] => eqb (length_ subm) 1
  | _ => false
  end.


#[global] Instance phantom_booleq: XBoolEquable bool PhantomType := {eqb := fun _ _ => true}.

Derive Show for IDefault.
Derive Shrink for IDefault.
Derive GenSized for IDefault.


#[global] Instance mapping_Dec: forall {K V} 
    `{forall k1 k2 : K, Dec (k1 = k2)} 
    `{forall v1 v2 : V, Dec (v1 = v2)}  (m1 m2: mapping K V), Dec (m1 = m2).
intros.
esplit.
unfold decidable.
repeat decide equality.
apply H0. apply H.
Defined.

#[global] Instance array_Dec: forall {V} 
    `{forall v1 v2 : V, Dec (v1 = v2)}  (m1 m2: listArray V), Dec (m1 = m2).
intros.
esplit.
unfold decidable.
repeat decide equality.
apply H.
Defined.
