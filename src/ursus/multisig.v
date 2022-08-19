
Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String.
Require Import Setoid. 
Require Import ZArith.
Require Import QArith.
Require Import Coq.Program.Equality.
Require Import Lia.

Require Import FinProof.All.
Require Import UMLang.All.
Require Import UrsusStdLib.Solidity.All.
Require Import UrsusStdLib.Solidity.unitsNotations.
Require Import UrsusTVM.Solidity.All.
Require Import UrsusTVM.Solidity.UrsusDefinitions.
Require Import UrsusTVM.Solidity.ReverseTranslatorConstructions.

Require Import UMLang.UrsusLib.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.
(* Require Import UMLang.LocalClassGenerator.ClassGenerator. *)

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
Local Open Scope list_scope.

Definition MultisigWallet_ι_CustodianInfoL: list Type := [
  ( uint8) : Type;
  ( uint256) : Type
].
Inductive MultisigWallet_ι_CustodianInfoFields :=
| MultisigWallet_ι_CustodianInfo_ι_index  (*uint8*)
| MultisigWallet_ι_CustodianInfo_ι_pubkey  (*uint256*)
.
GlobalGeneratePruvendoRecord MultisigWallet_ι_CustodianInfoL MultisigWallet_ι_CustodianInfoFields.
Opaque MultisigWallet_ι_CustodianInfoLRecord.

Interfaces.

MakeInterface Class Itmp :=
{     
    claim : external PhantomType true ;
 }.
EndInterfaces.

Require Import UMLang.LocalClassGenerator.ClassGenerator.

Contract MultisigWallet ;

Sends To  Itmp ; 

Types 
  Record MultisigWallet_ι_Transaction := {
    MultisigWallet_ι_Transaction_ι_id : uint64;
    MultisigWallet_ι_Transaction_ι_confirmationsMask : uint32;
    MultisigWallet_ι_Transaction_ι_signsRequired : uint8;
    MultisigWallet_ι_Transaction_ι_signsReceived : uint8;
    MultisigWallet_ι_Transaction_ι_creator : uint256;
    MultisigWallet_ι_Transaction_ι_index : uint8;
    MultisigWallet_ι_Transaction_ι_dest : address;
    MultisigWallet_ι_Transaction_ι_value : uint128;
    MultisigWallet_ι_Transaction_ι_sendFlags : uint16;
    MultisigWallet_ι_Transaction_ι_payload : TvmCell;
    MultisigWallet_ι_Transaction_ι_bounce : boolean
  }
Record MultisigWallet_ι_UpdateRequest := {
    MultisigWallet_ι_UpdateRequest_ι_id : uint64;
    MultisigWallet_ι_UpdateRequest_ι_index : uint8;
    MultisigWallet_ι_UpdateRequest_ι_signs : uint8;
    MultisigWallet_ι_UpdateRequest_ι_confirmationsMask : uint32;
    MultisigWallet_ι_UpdateRequest_ι_creator : uint256;
    MultisigWallet_ι_UpdateRequest_ι_codeHash : uint256;
    MultisigWallet_ι_UpdateRequest_ι_custodians : ( mapping uint256 uint256 (* uint256[] *));
    MultisigWallet_ι_UpdateRequest_ι_reqConfirms : uint8;
};

Constants 

Definition FLAG_SEND_ALL_REMAINING : uint8 := Build_XUBInteger (128)
Definition FLAG_IGNORE_ERRORS : uint8 := Build_XUBInteger (2)
Definition FLAG_PAY_FWD_FEE_FROM_BALANCE : uint8 := Build_XUBInteger (1)
Definition MAX_CLEANUP_TXNS : uint256 := Build_XUBInteger (40)
Definition MAX_CUSTODIAN_COUNT : uint8 := Build_XUBInteger (32)
Definition EXPIRATION_TIME : uint64 := Build_XUBInteger (3600)
Definition MAX_QUEUED_REQUESTS : uint8 := Build_XUBInteger (5);
Record Contract := {
   #[static] _pubkey : uint256;
   #[static] _foo : uint256;
   m_ownerKey :  uint256;
   m_requestsMask :  uint256;
   m_transactions :  mapping ( uint64 )  (_ResolveName "MultisigWallet_ι_Transaction") ;
   m_custodians :  XHMap ( uint256 )( uint8 );
   m_custodianCount :  uint8;
   m_updateRequests :  XHMap ( uint64 ) (_ResolveName "MultisigWallet_ι_UpdateRequest" ) ;
   m_updateRequestsMask :  uint32;
   m_requiredVotes :  uint8;
   m_defaultRequiredConfirmations :  uint8
}.

UseLocal Definition _ := [
     uint32 ;
     XMaybe  (XProd ( uint64)( MultisigWallet_ι_UpdateRequestLRecord ) );
     boolean;
     uint64;
    MultisigWallet_ι_UpdateRequestLRecord;
     XMaybe  (MultisigWallet_ι_UpdateRequestLRecord );
     uint8;
     uint256;
    MultisigWallet_ι_TransactionLRecord;
     XMaybe  (MultisigWallet_ι_TransactionLRecord );
     XMaybe  (XProd ( uint64)( MultisigWallet_ι_TransactionLRecord ) );
     uint128;
     XMaybe  ( uint8 );
     XDefault MultisigWallet_ι_UpdateRequestLRecord;
     XDefault
  (uint64 **
   MultisigWallet_ι_UpdateRequestLRecord)
].
 
 #[private , nonpayable ]
Ursus Definition _deleteUpdateRequest (updateId :  uint64) (index :  uint8): UExpression PhantomType false .
   ::// new 'onee : uint32 @ "onee" := β #{1} ; _ | .
(*    :://m_updateRequestsMask &=  ~ ( !onee  << #index ) . *)

   :: // m_updateRequests := m_updateRequests ->delete ( #updateId ) .
   :://return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _getExpirationBound : UExpression ( uint64) false .
  ::// return_ (((* now - *) EXPIRATION_TIME) << (β #{32})) |.
Defined. 
 
#[private, pure]
Ursus Definition _setConfirmed (mask :  uint32) (custodianIndex :  uint8): UExpression ( uint32) false .
  ::// new 'maskL : uint32 @ "maskL" := #mask ; _|.
  ::// new 'onee  : uint32 @ "onee" := β #{1} ; _ |.
(*   ::// maskL |= (!onee << #custodianIndex) . *)
  :://return_ #mask |.
Defined. 
  
#[private, nonpayable]
Ursus Definition _confirmUpdate (updateId :  uint64) (custodianIndex :  uint8): UExpression PhantomType false .
  ::// new 'request : ( MultisigWallet_ι_UpdateRequestLRecord ) @ "request"  := m_updateRequests[#updateId]  ; _| .
(*   ::// { // !request -> MultisigWallet_ι_UpdateRequest_ι_signs | : ULValue  uint8} ++ . *)
(*   :://!request ->MultisigWallet_ι_UpdateRequest_ι_confirmationsMask := 
               _setConfirmed(!request ->confirmationsMask, #{custodianIndex}) . *)

(*   :://m_updateRequests [#updateId] := {} (* !{request} *) . *)
  :://return_ {} |.
Defined. 
  
 
#[private, nonpayable]
Ursus Definition _removeExpiredUpdateRequests : UExpression PhantomType true .
  ::// new 'marker : (  uint64 ) @ "marker"  := _getExpirationBound ( ) ; _| .
  ::// if ( m_updateRequests->empty() ) then { {_:UExpression _ true} } .  
  :://exit_ {} |.
  :://new ('updateId : uint64, 'req : MultisigWallet_ι_UpdateRequestLRecord ) @ ( "updateId" , "req" )  
         := m_updateRequests->min() ->get() ; _| .
  ::// new 'needCleanup : (  boolean ) @ "needCleanup"  := (!{updateId} <= !{marker}) ; _|.
  ::// if ( !{needCleanup} ) then { {_:UExpression _ true} } .
  :://tvm->accept() .
  :://while (!{needCleanup}) do 
   {
       {_:UExpression PhantomType true} } ; _ |.
        ::// _deleteUpdateRequest( {} , {} ) .
             (* ::// {} !updateId | .
             ::// !req->MultisigWallet_ι_UpdateRequest_ι_index | . *)
      ::// new 'reqOpt : (  optional  ( uint64 ** MultisigWallet_ι_UpdateRequestLRecord ) ) @ "reqOpt"  := m_updateRequests->next(!{updateId}) ; _ |.
      ::// if ( !{reqOpt}->hasValue() ) then { {_:UExpression _ true} } 
                                        else { {_:UExpression _ true} } .
        (* :://[ updateId , req ] := !reqOpt ->get() . *)
        (* :://needCleanup := (!{updateId} <= !{marker})  |. *)
         :://exit_ {} |.
         :://exit_ {} |.
         :://exit_ {} |.
         :://exit_ {} |.
        (* :://!{needCleanup} := FALSE  |. *)

  (* :://tvm->commit  |. *)

  :://return_ {} |.
Defined. 


#[private, nonpayable] 
Ursus Definition _initialize (owners : mapping uint256 uint256 ) 
                             (reqConfirms :  uint8)
                            : UExpression PhantomType true (* false *) .
  ::// new 'ownerCount : (  uint8 ) @ "ownerCount"  := (β #{0}) ; _|.
  :://m_ownerKey := #{owners}[(β #{0})] .
  ::// new 'len : (  uint256 ) @ "len" := {} ; _ | . (* #{owners}->length () ; _|. *)
  ::// new 'i : (  uint256 ) @ "i"  := (β #{0}) ; _ | .
  ::// while ((!{i} < !{len}) && (!{ownerCount} < MAX_CUSTODIAN_COUNT)) do 
        { {_: UExpression PhantomType true (* false *)} } ; _ |.
 
      ::// new 'key : (  uint256 ) @ "key"  := #{owners}[!{i}] ; _| .
      ::// if ( (~ ( m_custodians->exists(!{key}))) ) then { {_:UExpression _ true (* false *)} }  |.
      (* :://m_custodians[!{key}] := !{ownerCount} ++  . *)
      (* :://!{i} ++ . *)
         ::// exit_ {} | .
(* } *)
  :://m_defaultRequiredConfirmations := (!{ownerCount} <= {} (* #{reqConfirms} *)) ? {} (* (!ownerCount) *) : {} (* !{reqConfirms} *) . 
  :://m_requiredVotes := (!{ownerCount} <= (β #{2})) ? !{ownerCount} : (((!{ownerCount} * (β #{2})) + (β #{1})) / (β #{3})) .
  :://m_custodianCount := !{ownerCount} .
  :://return_ {} |.
Defined. 

#[private, nonpayable]
Ursus Definition onCodeUpgrade (newOwners :  mapping uint256 uint256 ) 
                               (reqConfirms :  uint8)
                               : UExpression PhantomType true .
  :://tvm->resetStorage() .
  :://_initialize (#{newOwners}, #{reqConfirms}) .
  :://return_ {} |.
Defined. 
 
#[public, view]
Ursus Definition getUpdateRequests : UExpression (mapping uint256 uint256 (* MultisigWallet_ι_UpdateRequestLRecord *)) false .
  ::// new 'bound : (  uint64 ) @ "bound"  := _getExpirationBound ( ) ; _ | .
 (*for ((uint64 updateId, UpdateRequest req): m_updateRequests) {
            if (updateId > bound) {
                updates.push(req);
            } *)

(*   ::// if ( (!{updateId} > !{bound}) ) then { {_:UExpression _ false} }  |. *)
(*   :://updates ->push(!{req})  |. *)
  :://return_ {} |.
Defined. 
 
#[public, nonpayable]
Ursus Definition executeUpdate (updateId :  uint64) (code :  TvmCell): UExpression PhantomType true .
  :://require_(m_custodians->exists(msg->pubkey()), %100) .
(*   ::// _removeExpiredUpdateRequests ( ) . *)
  ::// new 'requestOpt : (  XMaybe  (MultisigWallet_ι_UpdateRequestLRecord ) ) @ "requestOpt"  := m_updateRequests->fetch(#{updateId}) ; _ | .
  :://require_(!{requestOpt}->hasValue(), %115 ) .
  ::// new 'request : ( MultisigWallet_ι_UpdateRequestLRecord ) @ "request"  := !{requestOpt}->get() ; _ | .
   :://require_((tvm->hash(#{code})  == !{request}->MultisigWallet_ι_UpdateRequest_ι_codeHash ), %119 ) . 
  :://require_(m_requiredVotes <= (!{request}->MultisigWallet_ι_UpdateRequest_ι_signs ), %120 ) .
  :://tvm->accept() .
  :://_deleteUpdateRequest(#{updateId}, !{request}->MultisigWallet_ι_UpdateRequest_ι_index) .
  :://tvm->setcode(#{code})  .
  :://tvm->setCurrentCode(#{code})  .
  :://onCodeUpgrade(!{request}->MultisigWallet_ι_UpdateRequest_ι_custodians, !{request}->MultisigWallet_ι_UpdateRequest_ι_reqConfirms) .
  :://return_ {} |.
Defined. 

#[private, view]
Ursus Definition _findCustodian (senderKey :  uint256): UExpression ( uint8) true .
  ::// new 'custodianIndex : (  XMaybe  ( uint8 ) ) @ "custodianIndex"  := m_custodians->fetch(#{senderKey}) ; _ | .
  :://require_(!{custodianIndex}->hasValue(), %100 ) .
  :://return_ !{custodianIndex}->get() |.
Defined. 

#[private, pure]
Ursus Definition _checkBit (mask :  uint32) (index :  uint8): UExpression ( boolean) false .
  ::// new 'onee : uint32 @ "onee" := (β #{1}) ; _ | .
  :://return_ {} (* (#{mask} & !onee << #{index}) != (β #{0})) *) |.
Defined. 

#[private, pure]
Ursus Definition _isConfirmed (mask :  uint32) (custodianIndex :  uint8): UExpression ( boolean) false .
  :://return_ _checkBit(#{mask}, #{custodianIndex}) |.
Defined. 

#[public, nonpayable]
Ursus Definition confirmUpdate (updateId :  uint64): UExpression PhantomType true .
  ::// new 'index : (  uint8 ) @ "index"  := _findCustodian(msg->pubkey()) ; _ | .
(*   :://_removeExpiredUpdateRequests ( ) . *)
  ::// new 'requestOpt : (  XMaybe  (MultisigWallet_ι_UpdateRequestLRecord ) ) @ "requestOpt"  := m_updateRequests->fetch(#{updateId}) ; _ | .
  :://require_(!{requestOpt}->hasValue(), %115) .
(*   :://require_((~ ( (_isConfirmed((!{requestOpt}->  get  ())->MultisigWallet_ι_UpdateRequest_ι_confirmationsMask, !{index})))), %116) . *)
  :://tvm->accept() .
  :://_confirmUpdate(#{updateId}, !{index}) .
  :://return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _generateId : UExpression ( uint64) false .
  :://return_ {} (* ((uint64(now) << (β #{32})) | (tx->timestamp & (β #{0xFFFFFFFF}))) *) |.
Defined. 

#[private, pure]
Ursus Definition _setSubmitted (mask :  uint32) (custodianIndex :  uint8): UExpression ( uint32) false .
  :://return_ _setConfirmed(#{mask}, #{custodianIndex}) |.
Defined. 

#[private, pure]
Ursus Definition _isSubmitted (mask :  uint32) (custodianIndex :  uint8): UExpression ( boolean) false .
  :://return_ _checkBit(#{mask}, #{custodianIndex}) |.
Defined. 

#[public, nonpayable]
Ursus Definition submitUpdate (codeHash :  uint256) 
                              (owners :  mapping uint256 uint256) 
                              (reqConfirms :  uint8)
                              : UExpression ( uint64) true .
  ::// new 'sender : (  uint256 ) @ "sender"  := msg->pubkey() ; _ | .
  ::// new 'index : (  uint8 ) @ "index"  := _findCustodian(!{sender}) ; _ | .
  :://require_(((#{owners}->length () > {}) (*β #{0}*) && (#{owners}->length () <= {} (* MAX_CUSTODIAN_COUNT *))), %117) .
(*   :://_removeExpiredUpdateRequests ( ) . *)
  :://require_((~ ( _isSubmitted(m_updateRequestsMask, !{index}))), %113) .
  :://tvm->accept() .
  :://m_updateRequestsMask := _setSubmitted(m_updateRequestsMask, !{index}) .
  ::// new 'updateId : uint64 @ "uint64" := _generateId ( ) ; _ | .
(*   :://m_updateRequests[updateId] := UpdateRequest(updateId, !{index}, (β #{0}), (β #{0}), !{sender}, #{codeHash}, #{owners}, #{reqConfirms}) . *)
  :://_confirmUpdate ( !{updateId} , !{index} )  |.
Defined. 

(* #[public, view]
Ursus Definition getCustodians : UExpression (mapping uint256 uint256 (* MultisigWallet_ι_CustodianInfoLRecord *)) false .

(*   :://custodians->push ( CustodianInfo(!{index}, !{key}))  |. *)
  (* :://new ('key , 'index ) @ (  uint256 ,  uint8 )   |. *)
 ::// return_ {}.
Defined.  *)

#[public, view]
Ursus Definition getTransactionIds : UExpression ( mapping uint256 uint64 ) false .
       (*  for ((uint64 trId, ): m_transactions) {
            ids.push(trId); *)
 :://return_ {} |.
Defined. 

#[public, view]
Ursus Definition getTransactions : UExpression (mapping uint256 uint256 (* MultisigWallet_ι_TransactionLRecord *)) false .
  ::// new 'bound : (  uint64 ) @ "bound"  := _getExpirationBound ( ) ; _ | .
(* for ((uint64 id, Transaction txn): m_transactions) {
            // returns only not expired transactions
            if (id > bound) {
                transactions.push(txn);
            }
        } *)
::// return_ {} | .
Defined. 

#[public, view]
Ursus Definition getTransaction (transactionId :  uint64): UExpression uint256 (*MultisigWallet_ι_TransactionLRecord*) true .
  ::// new 'txnOpt : (  XMaybe  (MultisigWallet_ι_TransactionLRecord ) ) @ "txnOpt"  := m_transactions->fetch(#{transactionId}) ; _ | .
  :://require_(!{txnOpt}->hasValue(), %102 ) .

(* for ((uint64 id, Transaction txn): m_transactions) {
            // returns only not expired transactions
            if (id > bound) {
                transactions.push(txn);
            }
        } *)

  ::// new 'trans : uint256 @ "trans" := {} ; _ | .
  ::// return_ !{trans} | .
Defined. 

#[public, view]
Ursus Definition getParameters : UExpression ( uint8 **  uint8 **  uint64 **  uint128 **  uint8 **  uint8) false .

     ::// new 'maxQueuedTransactions : uint8 @ "maxQueuedTransactions" := MAX_QUEUED_REQUESTS ; _  | .
     ::// new 'maxCustodianCount : uint8 @ "maxCustodianCount" := MAX_CUSTODIAN_COUNT ; _  | .
     ::// new 'expirationTime : uint64 @ "expirationTime" := EXPIRATION_TIME ; _ | .
     ::// new 'minValue : uint128 @ "minValue" := (β #{0}) ; _ | .
     ::// new 'requiredTxnConfirms : uint8 @ "requiredTxnConfirms" := m_defaultRequiredConfirmations ; _ | .
     ::// new 'requiredUpdConfirms : uint8 @ "requiredUpdConfirms" := m_requiredVotes ; _ | .

  ::// return_ {} | . (* [ !maxQueuedTransactions , !maxCustodianCount, !expirationTime, 
                 !minValue, !requiredTxnConfirms, !requiredUpdConfirms ]   |. *)
Defined. 

#[public, pure]
Ursus Definition isConfirmed (mask :  uint32) (index :  uint8): UExpression ( boolean) false .
  ::// return_ _isConfirmed(#{mask}, #{index})  |.
Defined. 
 
#[private, pure]
Ursus Definition _decMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
   ::// new 'onee : uint256 @ "onee" := β #{1} ; _ | . 
   ::// new 'eight : uint256 @ "eight" := β #{8} ; _ | . 
  :://return_ {} (*#{mask} - (!onee << (!eight * #{index}))*) |.
Defined. 

#[private, nonpayable]
Ursus Definition _removeExpiredTransactions : UExpression PhantomType true .
  ::// new 'marker : (  uint64 ) @ "marker"  := _getExpirationBound ( ) ; _ |  .
  ::// if ( m_transactions ->empty ()) then { {_:UExpression _ true} } .  
      :://exit_ {} | .
  :://new ('trId : uint64, 'txn : MultisigWallet_ι_TransactionLRecord) @ ("trId", "txn")  := m_transactions ->min() ->get() ; _ | .
  ::// new 'needCleanup : (  boolean ) @ "needCleanup"  := (!{trId} <= !{marker}) ; _ | .
  ::// if ( !{needCleanup} ) then { {_:UExpression _ true} } .
      :://tvm->accept() .
      ::// new 'i : (  uint256 ) @ "i"  := (β #{0}) ; _ | .
      :://while ((!{needCleanup} && (!{i} < MAX_CLEANUP_TXNS))) do { {_:UExpression _ true} }  |.

         (* ::// i ++ . *)
         ::// m_requestsMask := _decMaskValue(m_requestsMask, !{txn} ->MultisigWallet_ι_Transaction_ι_index) .
         (* ::// m_transactions ->delete (!trId) . *)
         ::// new 'nextTxn : (  XMaybe  (XProd ( uint64)( MultisigWallet_ι_TransactionLRecord ) ) ) @ "nextTxn"  := m_transactions->next(!{trId}) ; _ | .
         ::// if ( !{nextTxn}->hasValue() ) then { {_:UExpression _ true} } 
                                            else { {_:UExpression _ true} } .
               (* :://[ trId , _ ] := !{nextTxn}->get() . *)
               (* :://!{needCleanup} := (!{trId} <= !{marker})  |. *)
               ::// exit_ {} | .

               (* ::// needCleanup := FALSE  |. *)
               ::// exit_ {} | .

        (* :://tvm->commit  |. *)
        ::// exit_ {} | .

  :://return_ {} |.
Defined. 

#[private, nonpayable]
Ursus Definition _confirmTransaction (transactionId :  uint64) 
                                     (txn : MultisigWallet_ι_TransactionLRecord ) 
                                     (custodianIndex :  uint8)
                                     : UExpression PhantomType false .
  ::// new 'eightt : uint8 @ "eightt" := (β #{1}) ; _ | .
  ::// new 'tmp : uint8 @ "tmp" := #{txn}->MultisigWallet_ι_Transaction_ι_signsReceived ; _ | .
  :://if ( ( !{tmp} +  !{eightt}) >= 
             #{txn}->MultisigWallet_ι_Transaction_ι_signsRequired)  
             then { {_:UExpression _ false} } 
             else { {_:UExpression _ false} }  |. 
  :://tvm->transfer(#{txn}->MultisigWallet_ι_Transaction_ι_dest, 
                    #{txn}->MultisigWallet_ι_Transaction_ι_value, 
                    #{txn}->MultisigWallet_ι_Transaction_ι_bounce, 
                    #{txn}->MultisigWallet_ι_Transaction_ι_sendFlags) . (* , 
                    #{txn}->MultisigWallet_ι_Transaction_ι_payload) . *)
  :://m_requestsMask := _decMaskValue(m_requestsMask, #{txn}->MultisigWallet_ι_Transaction_ι_index) .
  :://m_transactions := m_transactions | . (* ->delete ( #{transactionId} ) |. *)
  (* ::// {//#{txn}->MultisigWallet_ι_Transaction_ι_confirmationsMask | : ULValue uint32} := 
            _setConfirmed(#{txn}->MultisigWallet_ι_Transaction_ι_confirmationsMask, 
              #{custodianIndex}) . *)
(*   ::// {//#txn ->MultisigWallet_ι_Transaction_ι_signsReceived | : ULValue uint8} ++ . *)
(*   :://m_transactions[#{transactionId}] := #{txn}  |. *)

  :://return_ {} |.
Defined. 

#[public, nonpayable]
Ursus Definition confirmTransaction (transactionId :  uint64): UExpression PhantomType true .
  ::// new 'index : (  uint8 ) @ "index" := _findCustodian(msg->pubkey()) ; _ | .
(*   ::// _removeExpiredTransactions ( ) . *)
  ::// new 'txnOpt : (  XMaybe  (MultisigWallet_ι_TransactionLRecord ) ) @ "txnOpt"  := m_transactions->fetch(#{transactionId}) ;_|.
  :://require_(!{txnOpt}->hasValue(), %102) .
  ::// new 'txn : ( MultisigWallet_ι_TransactionLRecord ) @ "txn"  := !{txnOpt}->get() ;_|.
  :://require_((~ ( _isConfirmed(!{txn}->MultisigWallet_ι_Transaction_ι_confirmationsMask, !{index}))), %103) .
  :://tvm->accept() .
  :://_confirmTransaction(#{transactionId}, !{txn}, !{index}) .
  :://return_ {} |.
Defined. 
 
#[private, pure]
Ursus Definition _getSendFlags (value :  uint128) (allBalance :  boolean): UExpression ( uint8 ** uint128) false .
  ::// new 'valueL : uint128 @ "valueL" := #{value} ; _|.
  ::// new 'flags : ( uint8 ) @ "flags"  := (FLAG_IGNORE_ERRORS (* | FLAG_PAY_FWD_FEE_FROM_BALANCE *)) ; _| .
  ::// if ( #{allBalance} ) then { {_:UExpression _ false} } .
  (* :://flags := (FLAG_IGNORE_ERRORS | FLAG_SEND_ALL_REMAINING) . *)
       (* :://valueL := (β #{0})  |. *)
     :://return_ {} | .
 
  :://return_ [ !{flags}, !{valueL} ] |.
Defined. 
 
#[private, pure]
Ursus Definition _incMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
  ::// new 'onee : uint256 @ "onee" := β #{1} ; _|.
  ::// new 'eightt : uint256 @ "eightt" := β #{8} ; _|.
(*   ::// new 'indexx : uint256 @ "indexx" := (β #{index} ) ;_|. *)
  :://return_ (#{mask} + (!{onee} << (!{eightt} (* * (!{indexx}) *)))) |.
Defined. 

#[private, pure]
Ursus Definition _getMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint8) false .
  ::// new 'eightt : uint256 @ "eightt" := β #{8} ; _|.
(*   ::// new 'indexx : uint256 @ "indexx" := (β #{index} ) ;_|. *)

  :://return_ {} (* uint8(((#{mask} >> (!{eightt} * uint256(!{indexx}))) & (β #{0xFF}))) *) |.
Defined. 

#[public, nonpayable]
Ursus Definition submitTransaction (dest :  address) 
                                   (value :  uint128) 
                                   (bounce :  boolean) 
                                   (allBalance :  boolean) 
                                   (payload :  cell_)
                                   : UExpression ( uint64) true .
  ::// new 'senderKey : (  uint256 ) @ "senderKey"  := msg->pubkey() ;_|.
  ::// new 'index : (  uint8 ) @ "index"  := _findCustodian(!{senderKey}) ;_|.
(*   :://_removeExpiredTransactions ( ) . *)
  :://require_((_getMaskValue(m_requestsMask, !{index}) < MAX_QUEUED_REQUESTS), %113 ) ;_| .
  :://tvm->accept() .
  :://new ('flags : uint8, 'realValue : uint128) @ (  "flags" ,  "realValue" )  := _getSendFlags(#{value}, #{allBalance}) ;_|.
  ::// new 'requiredSigns : (  uint8 ) @ "requiredSigns"  := m_defaultRequiredConfirmations ;_|.
  :://if ( (!{requiredSigns} <= (β #{1})) ) then { {_:UExpression _ true} } else { {_:UExpression _ true} } .

  :://tvm->transfer(#{dest}, !{realValue}, #{bounce}, {} (* !{flags} *)(* , #{payload} *)) .
  :://exit_ (β #{0}) |.

  :://m_requestsMask := _incMaskValue(m_requestsMask, !{index}) .
  ::// new 'trId : (  uint64 ) @ "trId"  := _generateId ( )  ;_|.
  ::// new 'txn : ( MultisigWallet_ι_TransactionLRecord ) @ "txn"  := 
  [$
    !{trId} ⇒ {MultisigWallet_ι_Transaction_ι_id};
    (β #{0}) ⇒ {MultisigWallet_ι_Transaction_ι_confirmationsMask};
    !{requiredSigns} ⇒ {MultisigWallet_ι_Transaction_ι_signsRequired};
    (β #{0}) ⇒ {MultisigWallet_ι_Transaction_ι_signsReceived};
    !{senderKey} ⇒ {MultisigWallet_ι_Transaction_ι_creator};
    !{index} ⇒ {MultisigWallet_ι_Transaction_ι_index};
    #{dest} ⇒ {MultisigWallet_ι_Transaction_ι_dest};
    !{realValue} ⇒ {MultisigWallet_ι_Transaction_ι_value};
    (* !{flags} *) {} ⇒ {MultisigWallet_ι_Transaction_ι_sendFlags};
    #{payload} ⇒ {MultisigWallet_ι_Transaction_ι_payload};
    #{bounce} ⇒ {MultisigWallet_ι_Transaction_ι_bounce}
   $] ;_|.
  :://_confirmTransaction(!{trId}, !{txn}, !{index}) .
  :://exit_ !{trId} |.
::// return_ {} |.
Defined. 

#[public, view]
Ursus Definition sendTransaction (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint16) (payload :  cell_): UExpression PhantomType true .
  :://require_((m_custodianCount == (β #{1})), %108) .
  :://require_((msg->pubkey() == m_ownerKey), %100) .
  :://tvm->accept() .
  :://tvm->transfer(#{dest}, #{value}, #{bounce}, (#{flags} (* | FLAG_IGNORE_ERRORS *))(* , #{payload} *)) .
  :://return_ {} |.
Defined. 

#[public, nonpayable]
Ursus Definition constructor (owners : mapping uint256 uint256) (reqConfirms :  uint8): UExpression PhantomType true .
  :://require_((msg->pubkey() == tvm->pubkey()), %100 ) .
(*   ::// new 'zeroo : uint @ "zeroo" := β #{0} ; _|. *)
  :://require_( #{owners}->length () > {} (* !{zeroo}  && (#{owners}->length <=  MAX_CUSTODIAN_COUNT )*) , %117) .
  :://tvm->accept() .
  :://_initialize(#{owners}, #{reqConfirms}) .
  :://return_ {} |.
Defined. 
EndContract Implements (*интерфейсы*) .





