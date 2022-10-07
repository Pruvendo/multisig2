(*/Users/petrlarockin/Downloads/TON/solidity-coq-translator/ref*)
Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Contract MultisigWallet ;
Sends To (*need fix*) ; 
(* Inherits   ; *)
Types 
Record Transaction := {
  Transaction_ι_id :  uint64;
  Transaction_ι_confirmationsMask :  uint32;
  Transaction_ι_signsRequired :  uint8;
  Transaction_ι_signsReceived :  uint8;
  Transaction_ι_creator :  uint256;
  Transaction_ι_index :  uint8;
  Transaction_ι_dest :  address;
  Transaction_ι_value :  uint128;
  Transaction_ι_sendFlags :  uint16;
  Transaction_ι_payload :  TvmCell;
  Transaction_ι_bounce :  boolean;
  Transaction_ι_stateInit :  optional  ( TvmCell )
}
Record UpdateRequest := {
  UpdateRequest_ι_id :  uint64;
  UpdateRequest_ι_index :  uint8;
  UpdateRequest_ι_signs :  uint8;
  UpdateRequest_ι_confirmationsMask :  uint32;
  UpdateRequest_ι_creator :  uint256;
  UpdateRequest_ι_codeHash :  optional  ( uint256 );
  UpdateRequest_ι_custodians :  optional  (listArray uint256 );
  UpdateRequest_ι_reqConfirms :  optional  ( uint8 );
  UpdateRequest_ι_lifetime :  optional  ( uint64 )
}
Record CustodianInfo := {
  CustodianInfo_ι_index :  uint8;
  CustodianInfo_ι_pubkey :  uint256
};
Constants 
Definition FLAG_SEND_ALL_REMAINING : uint8 := Build_XUBInteger (128)
Definition FLAG_IGNORE_ERRORS : uint8 := Build_XUBInteger (2)
Definition FLAG_PAY_FWD_FEE_FROM_BALANCE : uint8 := Build_XUBInteger (1)
Definition MAX_CLEANUP_TXNS : uint256 := Build_XUBInteger (40)
Definition MAX_CUSTODIAN_COUNT : uint8 := Build_XUBInteger (32)
Definition DEFAULT_LIFETIME : uint64 := Build_XUBInteger (3600)
Definition MAX_QUEUED_REQUESTS : uint8 := Build_XUBInteger (5);
Record Contract := {
   #[static] botch1: uint256;
   #[static] botch2: uint256;
    m_ownerKey: uint256;
    m_requestsMask: uint256;
    m_transactions: mapping  ( uint64 )(( _ResolveName "Transaction") );
    m_custodians: mapping  ( uint256 )( uint8 );
    m_custodianCount: uint8;
    m_updateRequests: mapping  ( uint64 )(( _ResolveName "UpdateRequest") );
    m_updateRequestsMask: uint32;
    m_requiredVotes: uint8;
    m_defaultRequiredConfirmations: uint8;
    m_lifetime: uint64
}.
UseLocal Definition _ := [
     optional  (tuple ( uint64)( UpdateRequestLRecord ) );
     boolean;
     uint64;
    UpdateRequestLRecord;
     TvmCell;
     uint8;
     optional  (UpdateRequestLRecord );
     uint256;
    TransactionLRecord;
     optional  (TransactionLRecord );
     optional  (tuple ( uint64)( TransactionLRecord ) );
     uint128;
     optional  ( uint8 );
     listArray uint256;
     listArray UpdateRequestLRecord;
     (optional uint256);
     (listArray CustodianInfoLRecord);
     (listArray TransactionLRecord);
     uint32
].
(* TODO -1 *)
Context `{listInfiniteFunRec_gen XList}.
#[private, nonpayable]
Ursus Definition _deleteUpdateRequest (updateId :  uint64) (index :  uint8): UExpression PhantomType false .
   ::// m_updateRequestsMask &= ((~)( (uint32(#{1}) << #{index}))) .
   ::// m_updateRequests[#{updateId}] ->delete .
   :://return_ {} |.
Defined. 

#[private, view]
Ursus Definition _getExpirationBound : UExpression ( uint64) false .
   :://return_ ((uint64(now) - m_lifetime) << #{32}) |.
Defined. 
Sync.

#[private, nonpayable]
Ursus Definition _removeExpiredUpdateRequests : UExpression PhantomType true .
   ?::// new 'marker : _  := _getExpirationBound ( ) ;_|.
   ::// if ( m_updateRequests->empty() ) then { ->/> } . 
      { :://exit_ {} |. }
   ::// new ('updateId : uint64, 'req : UpdateRequestLRecord ) @ ( "updateId" , "req" )  := m_updateRequests->min()->get() ; _| . 
   ?::// new 'needCleanup : _  := (^updateId <= ^marker) ; _ | .
   ::// if ( ^needCleanup ) then {  ->/> } .
      { ::// tvm->accept() .
        ::// while (^needCleanup) do { ->/> } ; _ |. 
          { ::// _deleteUpdateRequest( ^updateId , ^req->UpdateRequest_ι_index  ) .
            ?::// new 'reqOpt : _  :=  m_updateRequests->next(^updateId);_|. 
            :://if ( ^reqOpt->hasValue() ) then { ->/> } else { ->> } |.
               { ::// [ updateId, req ] := ^reqOpt->get() . 
                 ::// needCleanup := (^updateId <= ^marker)  |. } 
               { ::// needCleanup := @false  | . } 
          }
        :://tvm->commit()  |. 
      }
   :://return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _setConfirmed (mask :  uint32) (custodianIndex :  uint8): UExpression ( uint32) false .
   vararg mask "mask".
   ::// {mask} |= (uint32(#{1}) << #{custodianIndex}) .
   :://return_ !{mask} |.
Defined. 
Sync.

#[private, nonpayable]
Ursus Definition _confirmUpdate (updateId :  uint64) (custodianIndex :  uint8): UExpression PhantomType false .
   ?::// new 'request : _  :=  m_updateRequests[#{updateId}];_| .
   ::// {request}->UpdateRequest_ι_signs ++ .
   ::// {request}->UpdateRequest_ι_confirmationsMask := _setConfirmed(!{request}->UpdateRequest_ι_confirmationsMask, #{custodianIndex}) .
   ::// m_updateRequests := m_updateRequests->set(#{updateId}, !{request}) .
   :://return_ {} |.
Defined. 

#[private, nonpayable]
Ursus Definition _initialize (ownersOpt :  optional  ( listArray uint256 )) (reqConfirmsOpt :  optional  ( uint8 )) (lifetimeOpt :  optional  ( uint64 )): UExpression PhantomType true .
   ::// if ( #{ownersOpt}->hasValue() ) then { {_:UExpression _ true} } .
   ?::// new 'ownerCount : _ := uint8(#{0}) ;_|.
   ?::// new 'owners : _ := #{ownersOpt}->get() ;_|.
   ::// m_ownerKey := !{owners}[(#{0})]->get() ;_|.
   ?::// new 'len : _  := uint256(!{owners}->length()) ;_|.
   (* TODO 1 *)
   (* :://( ( m_custodians)) ->delete . *)
   ?::// new 'i : uint256  := uint256(#{0}) ;_|.
   ::// while ((!{i} < !{len}) && (!{ownerCount} < MAX_CUSTODIAN_COUNT)) do  { {_: UExpression PhantomType true } } ; _ |.
      ?::// new 'key : _ :=  !{owners}[!{i}]->get() ;_|.
      ::// if ( ((!) ( m_custodians->exists(!{key}))) ) then { {_:UExpression _ false} }  .
         :://m_custodians:= m_custodians ->set(!{key}, !{ownerCount}).
         ::// {ownerCount} ++ |.

      ::// {i} ++ |.

   :://m_custodianCount := !{ownerCount}  |.

   ::// if ( #{reqConfirmsOpt}->hasValue() ) then { {_:UExpression _ true} } .
      ::// m_defaultRequiredConfirmations := math->min(m_custodianCount, #{reqConfirmsOpt}->get())  |.

   :://m_requiredVotes := (m_custodianCount <= uint8(#{2})) ? m_custodianCount : (((m_custodianCount * (β #{2})) + (β #{1})) / (β #{3})) .
   ::// if ( #{lifetimeOpt}->hasValue() ) then { {_:UExpression _ true} } .
      ?::// new 'newLifetime : _  := #{lifetimeOpt}->get();_| .
      ::// if ( (!{newLifetime} == uint64(#{0})) ) then { {_:UExpression _ false} } .
         ::// {newLifetime} := DEFAULT_LIFETIME  |.

      :://m_lifetime := !{newLifetime}  |.

   :://return_ {} |.
Defined. 
Sync.

#[private, nonpayable]
Ursus Definition onCodeUpgrade (newOwners :  listArray uint256) (reqConfirms :  uint8): UExpression PhantomType true .
   ::// tvm->resetStorage() .
   ::// _initialize(some(#{newOwners}), some(#{reqConfirms}), some(DEFAULT_LIFETIME)) .
   ::// return_ {} |.
Defined. 
Sync.


#[public, view]
Ursus Definition getUpdateRequests : UExpression (listArray UpdateRequestLRecord) false .
   ?::// new 'updates_ : listArray UpdateRequestLRecord   := newArray(0);_| .
   ?::// new 'bound : _  := _getExpirationBound( );_| .
   ::// for ( 'item : m_updateRequests ) do { {_:UExpression _ false} } .
   ::// new ('updateId: uint64 , 'req: UpdateRequestLRecord ) @ ("updateId", "req") := item ;_|.
       ::// if ( (!{updateId} > !{bound}) ) then { {_:UExpression _ false} }  |.
      :://{updates_}->push(!{req})  |.
   :://return_ !{updates_} |.
Defined. 
Sync.


#[public, nonpayable]
Ursus Definition executeUpdate (updateId :  uint64) (code :  optional  ( TvmCell )): UExpression PhantomType true .
   ::// require_(m_custodians->exists(msg->pubkey()), #{100}) .
   ::// _removeExpiredUpdateRequests( ) ;_|.
   ?::// new 'requestOpt : _  :=  m_updateRequests->fetch(#{updateId}) ;_|.
   ::// require_(!{requestOpt}->hasValue(), #{115}) .
   ?::// new 'request : _  := !{requestOpt}->get() ;_|.
   ::// if ( !{request}->UpdateRequest_ι_codeHash->hasValue() ) then { {_:UExpression _ true} } else { {_:UExpression _ true} } ;_|.
   ::// require_(#{code}->hasValue(), #{119}) .
   :://require_((tvm->hash(#{code}->get_default())  == ((!{request}->UpdateRequest_ι_codeHash)->get_default())), #{119})  |.
   ::// require_(((!)( #{code}->hasValue())), #{125})  |.
   :://require_( ((!{request}->UpdateRequest_ι_signs) >=  (m_requiredVotes)), #{120}) .
   ::// tvm->accept() .
   ::// _deleteUpdateRequest(#{updateId}, !{request}->UpdateRequest_ι_index) .
   ::// if ( !{request}->UpdateRequest_ι_codeHash->hasValue() ) then { {_:UExpression _ true} } else { {_:UExpression _ true} } .
   ::// tvm->commit() .
   ::// new 'newReqConfirms : uint8 @ "newReqConfirms" := !{request}->UpdateRequest_ι_reqConfirms->hasValue() ? !{request}->UpdateRequest_ι_reqConfirms->get() : m_defaultRequiredConfirmations;_| .
   ::// new 'newcode : TvmCell @ "newcode" := #code->get() ; _ | .
   :://tvm->setcode(!{newcode})  .
   :://tvm->setCurrentCode(!{newcode})  .
   :://onCodeUpgrade( !{request}->UpdateRequest_ι_custodians->get(), !{newReqConfirms})  |.
   :://_initialize((!{request}->UpdateRequest_ι_custodians) , (!{request}->UpdateRequest_ι_reqConfirms), (!{request}->UpdateRequest_ι_lifetime))  |.
   :://return_ {} |.
Defined. 

#[private, view]
Ursus Definition _findCustodian (senderKey :  uint256): UExpression ( uint8) true .
   ?::// new 'custodianIndex : _  := m_custodians->fetch(#{senderKey}) ;_|.
   :://require_(!{custodianIndex}->hasValue(), #{100}) .
   :://return_ !{custodianIndex}->get() |.
Defined. 

#[private, pure]
Ursus Definition _checkBit (mask :  uint32) (index :  uint8): UExpression ( boolean) false .
   :://return_ ((uint32(#{mask}) & (uint32(#{1}) << #{index})) != uint32(#{0})) |.
Defined. 
Sync.

#[private, pure]
Ursus Definition _isConfirmed (mask :  uint32) (custodianIndex :  uint8): UExpression ( boolean) false .
   :://return_ _checkBit(#{mask}, #{custodianIndex}) |.
Defined. 
Sync.

#[public, nonpayable]
Ursus Definition confirmUpdate (updateId :  uint64): UExpression PhantomType true .
   ?::// new 'index : _  := _findCustodian(msg->pubkey()) ;_|.
   :://_removeExpiredUpdateRequests( ) .
   ?::// new 'requestOpt : _  :=  m_updateRequests->fetch(#{updateId}) ;_|.
   :://require_(!{requestOpt}->hasValue(), #{115}) .
   :://require_(((!)( _isConfirmed(!{requestOpt}->get_default()->UpdateRequest_ι_confirmationsMask, !{index}))), #{116}) .
   :://tvm->accept() .
   :://_confirmUpdate(#{updateId}, !{index}) .
   :://return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _generateId : UExpression ( uint64) false .
   :://return_ ((uint64(now) << #{32}) \ (tx->timestamp & #{0xFFFFFFFF})) |.
Defined. 

#[private, pure]
Ursus Definition _setSubmitted (mask :  uint32) (custodianIndex :  uint8): UExpression ( uint32) false .
   :://return_ _setConfirmed(#{mask}, #{custodianIndex}) |.
Defined. 

#[private, pure]
Ursus Definition _isSubmitted (mask :  uint32) (custodianIndex :  uint8): UExpression ( boolean) false .
   :://return_ _checkBit(#{mask}, #{custodianIndex}) |.
Defined. 

Sync.

#[public, nonpayable]
Ursus Definition submitUpdate (codeHash :  optional  ( uint256 )) (owners :  optional  ( listArray uint256 )) (reqConfirms :  optional  ( uint8 )) (lifetime :  optional  ( uint64 )): UExpression ( uint64) true .
   ?::// new 'codeHash_ : _  := #{codeHash};_|.
   ?::// new 'sender : _  := msg->pubkey();_|.
   ?::// new 'index : _  := _findCustodian(!{sender});_| .
   ::// if ( !{codeHash_}->hasValue() ) then { {_:UExpression _ true} } .
   :://require_(#{owners}->hasValue(), #{124})  |.

   ::// if ( #{owners}->hasValue() ) then { {_:UExpression _ true} } .

   ?::// new 'newOwnerCount :_  := uint256(#{owners}->get()->length());_| .
   :://require_(((!{newOwnerCount} > uint256(#{0})) && (!{newOwnerCount} <= uint256(MAX_CUSTODIAN_COUNT))), #{117})  |.
   :://_removeExpiredUpdateRequests( ) .
   :://require_(((!)( _isSubmitted(m_updateRequestsMask, !{index}))), #{113}) .
   :://tvm->accept() .
   ::// if ( !{codeHash_}->hasValue() ) then { {_:UExpression _ false} } .
   ::// if ( (!{codeHash_}->get_default() == tvm->hash(tvm->code()) ) ) then { {_:UExpression _ false} }  |.
      ::// {codeHash_} ->reset() |.

   ::// m_updateRequestsMask := _setSubmitted(m_updateRequestsMask, !{index}) .
   ?::// new 'updateId :_  := _generateId( ) ;_|.
   :://m_updateRequests := m_updateRequests->set(!{updateId}, [ !{updateId} , !{index}  ,
                      uint8(#{0})  , 
                      uint32(#{0})  ,
                      !{sender}  , 
                      !{codeHash_}  ,
                      #{owners}  , 
                      #{reqConfirms}  , 
                      #{lifetime} ] ) ;_| .
   :://_confirmUpdate(!{updateId}, !{index})  .
   ::// return_ !{updateId} |.
Defined. 

#[public, view]
Ursus Definition getCustodians : UExpression (listArray CustodianInfoLRecord) false .
   ?::// new 'custodians : listArray CustodianInfoLRecord := newArray(0) ;_|.
   ::// for ( 'item : m_custodians ) do { {_:UExpression _ false} } .
   ::// new ('key: uint256 , 'index: uint8 ) @ ("key", "index") := item ;_|.
   ::// {custodians}->push([ !{index}, !{key} ])|.
   :://return_ !{custodians} |.
Defined. 

#[public, view]
Ursus Definition getTransactions : UExpression (listArray TransactionLRecord) false .
?::// new 'transactions: (listArray TransactionLRecord) := newArray(0);_|.
?::// new 'bound : _  := _getExpirationBound( );_| .
   ::// for ( 'item : m_transactions ) do { {_:UExpression _ false} } .
         ::// new ('id: uint64 , 'txn:  TransactionLRecord ) @ ("updateId", "req") := item ;_|. 
         ::// if ( (!{id} > !{bound}) ) then { {_:UExpression _ false} }  |.
            :://transactions->push(!{txn})  |. 
   :://return_ !{transactions} |.
Defined. 

#[public, view]
Ursus Definition getTransaction (transactionId :  uint64): UExpression (TransactionLRecord) true .
   ?::// new 'txnOpt : _  := m_transactions->fetch(#{transactionId}) ;_|.
   :://require_(!{txnOpt}->hasValue(), #{102}) .
   ::// (*trans :=*) return_ !{txnOpt}->get()  |.
Defined. 





#[public, view]
Ursus Definition getParameters : UExpression ( uint8 **  uint8 **  uint64 **  uint128 **  uint8 **  uint8) false .
   (* :://maxQueuedTransactions := MAX_QUEUED_REQUESTS .
   :://maxCustodianCount := MAX_CUSTODIAN_COUNT .
   :://expirationTime := m_lifetime .
   :://minValue := #{0} .
   :://requiredTxnConfirms := m_defaultRequiredConfirmations .
   :://requiredUpdConfirms := m_requiredVotes  |. *)
   ::// return_ [  MAX_QUEUED_REQUESTS, 
                   MAX_CUSTODIAN_COUNT, 
                   m_lifetime, 
                   uint128(#{0}), 
                   m_defaultRequiredConfirmations, 
                   m_requiredVotes ] |.
Defined. 

#[public, pure]
Ursus Definition isConfirmed (mask :  uint32) (index :  uint8): UExpression ( boolean) false .
   :://(*confirmed :=*) return_ _isConfirmed(#{mask}, #{index})  |.
Defined. 

Sync.

#[private, pure]
Ursus Definition _decMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
   :://return_ (#{mask} - (#{1} << (#{8} * uint256(#{index})))) |.
Defined. 

Sync.

#[private, nonpayable]
Ursus Definition _removeExpiredTransactions : UExpression PhantomType true .
   ?::// new 'marker : _  := _getExpirationBound( );_| .
   ::// if ( m_transactions->empty() ) then { {_:UExpression _ true} } .
      :://exit_ {} |.
   ::// new ('trId: uint64 , 'txn: TransactionLRecord ) @ (  "trId" ,"txn"  )  := m_transactions->min() ->get();_| .
   ?::// new 'needCleanup : _ := (!{trId} <= !{marker});_| .
   ::// if ( !{needCleanup} ) then { {_:UExpression _ true} } .
      ::// tvm->accept() .
      ?::// new 'i : _  := uint256(#{0});_ |.
      :://while ((!{needCleanup} && (!{i} < MAX_CLEANUP_TXNS))) do { {_: UExpression PhantomType true } } ; _ |.

         :://{i} ++ .
         :://m_requestsMask := _decMaskValue(m_requestsMask, !{txn}->Transaction_ι_index).
         ::// m_transactions[!{trId}] ->delete.
         ?:://new 'nextTxn : _  :=  m_transactions->next(!{trId});_|.
         ::// if ( !{nextTxn}->hasValue() ) then { {_:UExpression _ true} } else { {_:UExpression _ false} } |.
            ?::// new 'botch3 : TransactionLRecord := {} ; _ |.
            ::// [ {trId}, {botch3} ] := !{nextTxn}->get() .
            ::// {needCleanup} := (!{trId} <= !{marker})  |.

            :://{needCleanup} := FALSE  |.

      :://tvm->commit()  |.

   :://return_ {} |.
Defined. 
Sync.

#[private, nonpayable]
Ursus Definition _confirmTransaction (txn : TransactionLRecord) (custodianIndex :  uint8): UExpression PhantomType false .
   vararg txn "txn".
   :://if (  ((!{txn}->Transaction_ι_signsReceived + (uint8(#{1}))) >= !{txn}->Transaction_ι_signsRequired) ) then { {_:UExpression _ false} } else { {_:UExpression _ false} }  .
   :://if ( !{txn}->Transaction_ι_stateInit->hasValue() ) then { {_:UExpression _ false} } else { {_:UExpression _ false} }  .
   :://tvm->transfer(
         !{txn}->Transaction_ι_dest, 
         !{txn}->Transaction_ι_value, 
         !{txn}->Transaction_ι_bounce, 
         !{txn}->Transaction_ι_sendFlags,
         !{txn}->Transaction_ι_payload) |.

   :://tvm->transfer(
         !{txn}->Transaction_ι_dest, 
         !{txn}->Transaction_ι_value, 
         !{txn}->Transaction_ι_bounce, 
         !{txn}->Transaction_ι_sendFlags,         
         !{txn}->Transaction_ι_payload)  |.

   :://m_requestsMask := _decMaskValue(m_requestsMask, !{txn}->Transaction_ι_index) .
   :://m_transactions[!{txn}->Transaction_ι_id]->delete  |.
   
   :://{txn}->Transaction_ι_confirmationsMask := _setConfirmed(!{txn}->Transaction_ι_confirmationsMask, #{custodianIndex}) .
   :://{txn}->Transaction_ι_signsReceived ++ .
   :://m_transactions:= m_transactions->set(!{txn}->Transaction_ι_id, !{txn})  |.
   :://return_ {} |.
Defined. 
Sync.

#[public, nonpayable]
Ursus Definition confirmTransaction (transactionId :  uint64): UExpression PhantomType true .
   ?::// new 'index : _ := _findCustodian(msg->pubkey()) ;_|.
   :://_removeExpiredTransactions( ) .
   ?::// new 'txnOpt : _  :=  m_transactions->fetch(#{transactionId});_| .
   :://require_(!{txnOpt}->hasValue(), #{102}) .
   ?::// new 'txn : _  := !{txnOpt}->get();_| .
   :://require_(((!)( _isConfirmed(!{txn}->Transaction_ι_confirmationsMask, !{index}))), #{103}) .
   :://tvm->accept() .
   :://_confirmTransaction(!{txn}, !{index}) .
   :://return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _getSendFlags (value :  uint128) (allBalance :  boolean): UExpression ( uint8 ** uint128) false .
   ?::// new 'value_ : _  := #{value} ;_|.
   ?::// new 'flags : _  := (FLAG_IGNORE_ERRORS \ FLAG_PAY_FWD_FEE_FROM_BALANCE);_|.
   ::// if ( #{allBalance} ) then { {_:UExpression _ false} } .
   ::// {flags} := (FLAG_IGNORE_ERRORS \ FLAG_SEND_ALL_REMAINING).
   ::// {value_ } := uint128(#{0})  |.

   :://return_ [ !{flags}, !{value_} ] |.
Defined. 

#[private, pure]
Ursus Definition _incMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
   :://return_ (#{mask} + (#{1} << (#{8} * uint256(#{index})))) |.
Defined. 

#[private, pure]
Ursus Definition _getMaskValue (mask :  uint256) (index :  uint8): UExpression ((*TODO*) uint256) false .
   :://return_ (((#{mask} >> (#{8} * uint256(#{index}))) & #{0xFF})) |.
Defined. 
Sync.

#[public, nonpayable]
Ursus Definition submitTransaction (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  TvmCell) (stateInit :  optional  ( TvmCell )): UExpression ( uint64) true .
   ?::// new 'senderKey : _  := msg->pubkey() ;_|.
   ?::// new 'index : _  := _findCustodian(!{senderKey}) ;_|.
   :://_removeExpiredTransactions( ) .
   :://require_((_getMaskValue(m_requestsMask, !{index}) < uint256(MAX_QUEUED_REQUESTS)), #{113}) .
   :://tvm->accept() .
   :://new ('flags: uint8 , 'realValue: uint128 ) @ (  "flags" ,  "realValue" )  := _getSendFlags(#{value}, #{allBalance}) ;_|.
   :://m_requestsMask := _incMaskValue(m_requestsMask, !{index}) .
   ?::// new 'trId : _  := _generateId( ) ;_|.
   (* TODO 7 - done ??*)
   (* Compute TransactionLRecord. *)

   (* Transaction txn = Transaction({
            id: trId,
            confirmationsMask: 0,
            signsRequired: m_defaultRequiredConfirmations,
            signsReceived: 0,
            creator: senderKey,
            index: index,
            dest: dest, 
            value: realValue,
            sendFlags: flags,
            payload: payload,
            bounce: bounce,
            stateInit: stateInit *)
   (*почему-то sendFlags имеет тип uint16, но передается ему uint8*)
   ?::// new 'txn :  TransactionLRecord  := [!{trId}, 
                                             uint32(#{0}), 
                                             m_defaultRequiredConfirmations, 
                                             uint8(#{0}), 
                                             !{senderKey}, 
                                             !{index}, 
                                             #{dest}, 
                                             !{realValue}, 
                                             uint16(!{flags}), 
                                             #{payload}, 
                                             #{bounce}, 
                                             #{stateInit} ];_|.
   :://_confirmTransaction(!{txn}, !{index}) .
   :://return_ !{trId} |.
Defined. 

#[public, view]
Ursus Definition sendTransaction (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint8) (payload :  TvmCell): UExpression PhantomType true .
   :://require_((m_custodianCount == uint8(#{1})), #{108}) .
   :://require_((msg->pubkey() == m_ownerKey), #{100}) .
   :://tvm->accept() .
   :://tvm->transfer(#{dest}, #{value}, #{bounce}, uint16(#{flags} \ FLAG_IGNORE_ERRORS), #{payload}) .
   :://return_ {} |.
Defined. 

#[public, nonpayable]
Ursus Definition constructor (owners :  listArray uint256) (reqConfirms :  uint8) (lifetime :  uint32): UExpression PhantomType true .
   ::// if ( (msg->sender->value == uint256(#{0})) ) then { {_:UExpression _ true} } .
   :://require_((msg->pubkey() == tvm->pubkey()), #{100})  |.
   :://require_((#{lifetime} > uint32(#{0})), #{123}) .
   :://require_(((uint8(#{owners}->length()) > uint8(#{0}))  && (uint8(#{owners}->length()) <= uint8(MAX_CUSTODIAN_COUNT))), #{117}) .
   :://tvm->accept() .
   :://_initialize(some(#{owners}), some(#{reqConfirms}), some(uint64(#{lifetime}))) .
   :://return_ {} |.
Defined. 
EndContract Implements (*interfaces*) .