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
Definition MIN_LIFETIME : uint32 := Build_XUBInteger (10)
Definition DEFAULT_LIFETIME : uint32 := Build_XUBInteger (3600)
Definition MAX_QUEUED_REQUESTS : uint8 := Build_XUBInteger (5);
Record Contract := {
    #[static] FIXME: uint256;
    #[static] andruiman: uint256;
    m_ownerKey: uint256;
    m_requestsMask: uint256;
    m_transactions: mapping  ( uint64 )((_ResolveName "Transaction") );
    m_custodians: mapping  ( uint256 )( uint8 );
    m_custodianCount: uint8;
    m_defaultRequiredConfirmations: uint8;
    m_lifetime: uint32
}.
UseLocal Definition _ := [
     uint256;
     uint8;
     uint64;
    (TransactionLRecord);
     optional  ((TransactionLRecord) );
     optional  (tuple ( uint64)( (TransactionLRecord) ) );
     boolean;
     uint128;
     optional  ( uint8 );
     uint32;
     uint256[];

     (optional uint256);
     (listArray CustodianInfoLRecord);
     (listArray TransactionLRecord);
     uint32
].

Context `{listInfiniteFunRec_gen XList}.
#[external, view]
Ursus Definition getCustodians : UExpression (CustodianInfoLRecord[]) false .
   ?::// new 'custodians : listArray CustodianInfoLRecord := newArray(0) ;_|.
   ::// for ( 'item : m_custodians ) do { {_:UExpression _ false} } .
      ::// new ('key: uint256 , 'index: uint8 ) @ ("key", "index") := item ;_|.
      ::// {custodians}->push([ !{index}, !{key} ])|.
   :://return_ !{custodians} |.
Defined. 

#[private, pure]

Ursus Definition _checkBit (mask :  uint32) (index :  uint8): UExpression ( boolean) false .
    :://  return_ ((uint32(#{mask}) & (uint32(#{1}) << uint32(#{index}))) != uint32(#{0})) |.
Defined. 

#[private, view]
Ursus Definition _getExpirationBound : UExpression ( uint64) false .
    :://  return_ ((uint64(now) - uint64(m_lifetime)) << #{32}) |.
Defined. 

#[external, view]
Ursus Definition getTransactions : UExpression ((TransactionLRecord[])) false .
    ?::// new 'transactions : listArray TransactionLRecord := newArray(0) ;_|.
    ?::// new 'bound :  uint64  := _getExpirationBound( );_|.
    :://  for ('item :m_transactions) do { {_:UExpression _ false} }   .
    {
        ::// new ('id: uint64 , 'txn: TransactionLRecord ) @ ("id", "txn") := item ;_|.
        :://  if ( ( ^{id} > ^{bound}) ) then { {_:UExpression _ false} }  |.
        {
            :://  transactions->push(^{txn})  |.
        }
    }
    ::// return_ ^transactions|.
Defined. 

#[external, view]
Ursus Definition getTransaction (transactionId :  uint64): UExpression ((TransactionLRecord)) true .
    ?::// new 'txnOpt :  optional  ((TransactionLRecord) )  := m_transactions->fetch(#transactionId);_|.
    :://  require_(^txnOpt->hasValue(), #{102}) .
    :://  (*trans :=*) return_ ^txnOpt->get()  |.
Defined. 

(*         returns (uint8 maxQueuedTransactions,
                uint8 maxCustodianCount,
                uint64 expirationTime,
                uint128 minValue,
                uint8 requiredTxnConfirms) {

        maxQueuedTransactions = MAX_QUEUED_REQUESTS;
        maxCustodianCount = MAX_CUSTODIAN_COUNT;
        expirationTime = m_lifetime;
        minValue = 0;
        requiredTxnConfirms = m_defaultRequiredConfirmations; *)

#[external, view]
Ursus Definition getParameters : UExpression ( uint8 **  uint8 **  uint64 **  uint128 **  uint8) false .
    (* :://  maxQueuedTransactions := MAX_QUEUED_REQUESTS .
    :://  maxCustodianCount := MAX_CUSTODIAN_COUNT .
    :://  expirationTime := m_lifetime .
    :://  minValue := #0 .
    :://  requiredTxnConfirms := m_defaultRequiredConfirmations  |. *)
    ::// return_ [  MAX_QUEUED_REQUESTS,  MAX_CUSTODIAN_COUNT,  uint64(m_lifetime),  uint128(#{0}), m_defaultRequiredConfirmations] |.
Defined. 

#[private, pure]
Ursus Definition _isConfirmed (mask :  uint32) (custodianIndex :  uint8): UExpression ( boolean) false .
    :://  return_ _checkBit(#{mask}, #custodianIndex) |.
Defined. 

#[external, pure]
Ursus Definition isConfirmed (mask :  uint32) (index :  uint8): UExpression ( boolean) false .
    :://  return_ (*confirmed :=*) _isConfirmed(#{mask}, #{index})  |.
Defined. 

#[private, pure]
Ursus Definition _decMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
    :://  return_ (#{mask} - (#{1} << (#{8} * uint256(#{index})))) |.
Defined. 

#[private, nonpayable]
Ursus Definition _removeExpiredTransactions : UExpression PhantomType true .
    ?::// new 'marker :  uint64  := _getExpirationBound( );_|.
    :://  if ( m_transactions->empty() ) then { {_:UExpression _ true} } .
    {
        :://  exit_ {} |.
    }
    ::// new ('trId: uint64 , 'txn: TransactionLRecord ) @ (  "trId" ,"txn"  )  := m_transactions->min() ->get();_| .
    ?::// new 'needCleanup :  boolean  := (^trId <= ^marker);_|.
    :://  if ( ^needCleanup ) then { {_:UExpression _ true} } .
    {
        :://  tvm->accept() .
        ?::// new 'i :  uint256  := uint256(#{0});_|.
        :://  while ((^needCleanup && (^i < MAX_CLEANUP_TXNS))) do { {_:UExpression _  true} }  ;_|.
            :://  i ++ .
            :://  m_requestsMask := _decMaskValue(m_requestsMask, ^{txn}->Transaction_ι_index) .
            :://  m_transactions[^trId] ->delete .
            ?::// new 'nextTxn :  optional  (tuple ( uint64)( (TransactionLRecord) ) )  := m_transactions->next(^trId);_|.
            :://  if ( ^nextTxn->hasValue() ) then { {_:UExpression _ true} } else { {_:UExpression _ false} }  |.
            {   
                ?::// new 'botch3 : TransactionLRecord := {} ; _ |.
                ::// [ {trId}, {botch3} ] := !{nextTxn}->get() .
                :://  needCleanup := (^trId <= ^marker)  |.
            }
            {
                :://  needCleanup := @false  |.
            }
        :://  tvm->commit()  |.
    }
    :://  return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _setConfirmed (mask :  uint32) (custodianIndex :  uint8): UExpression ( uint32) false .
    vararg mask "mask".
    :://  mask |= (uint32(#{1}) << #{custodianIndex}) .
    :://  return_ ^mask |.
Defined. 

#[private, nonpayable]
Ursus Definition _confirmTransaction (txn : (TransactionLRecord)) (custodianIndex :  uint8): UExpression PhantomType false .
    vararg txn "txn".
    :://  if ( ((^txn->Transaction_ι_signsReceived + #{1}) >= ^txn->Transaction_ι_signsRequired) ) then { {_:UExpression _ false} } else { {_:UExpression _ false} } .
    {
        :://  if ( ^txn->Transaction_ι_stateInit->hasValue() ) then { {_:UExpression _ false} } else { {_:UExpression _ false} } .
        {
            :://  tvm->transfer(^txn->Transaction_ι_dest, 
                                ^txn->Transaction_ι_value, 
                                ^txn->Transaction_ι_bounce, 
                                ^txn->Transaction_ι_sendFlags, 
                                ^txn->Transaction_ι_payload) |.
                                (* ^txn->Transaction_ι_stateInit->get())  |. TODO *)
        }
        {
            :://  tvm->transfer(^txn->Transaction_ι_dest, 
                                ^txn->Transaction_ι_value, 
                                ^txn->Transaction_ι_bounce, 
                                ^txn->Transaction_ι_sendFlags, 
                                ^txn->Transaction_ι_payload) |.
        }
        :://  m_requestsMask := _decMaskValue(m_requestsMask, ^txn->Transaction_ι_index) .
        :://  m_transactions[^txn->Transaction_ι_id] ->delete  |.
    }
    {
        :://  {txn}->Transaction_ι_confirmationsMask := _setConfirmed(^txn->Transaction_ι_confirmationsMask, #custodianIndex) .
        :://  txn->Transaction_ι_signsReceived ++ |.
        (* :://  m_transactions[^txn->Transaction_ι_id] := ^txn  |. TODO *)
    }
    :://  return_ {} |.
Defined. 

#[private, view]
Ursus Definition _findCustodian (senderKey :  uint256): UExpression ( uint8) true .
    ?::// new 'custodianIndex :  optional  ( uint8 )  := m_custodians->fetch(#senderKey);_|.
    :://  require_(^custodianIndex->hasValue(), #{100}) .
    :://  return_ ^custodianIndex->get() |.
Defined. 

#[public, nonpayable]
Ursus Definition confirmTransaction (transactionId :  uint64): UExpression PhantomType true .
    ?::// new 'index :  uint8  := _findCustodian(msg->pubkey());_|.
    :://  _removeExpiredTransactions( ) .
    ?::// new 'txnOpt :  optional  ((TransactionLRecord) )  := m_transactions->fetch(#transactionId);_|.
    :://  require_(^txnOpt->hasValue(), #{102}) .
    ?::// new 'txn : (TransactionLRecord)  := ^txnOpt->get();_|.
    :://  require_(( (!) ( _isConfirmed(^txn->Transaction_ι_confirmationsMask, ^{index}))), #{103}) .
    :://  tvm->accept() .
    :://  _confirmTransaction(^txn, ^{index}) .
    :://  return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _getSendFlags (value :  uint128) (allBalance :  boolean): UExpression ( uint8 **  uint128) false .
    vararg value "value".
    ?::// new 'flags :  uint8  := (FLAG_IGNORE_ERRORS \ FLAG_PAY_FWD_FEE_FROM_BALANCE);_|.
    :://  if ( #allBalance ) then { {_:UExpression _ false} } .
    {
        :://  flags := (FLAG_IGNORE_ERRORS \ FLAG_SEND_ALL_REMAINING) .
        :://  {value} := uint128(#{0})  |.
    }
    :://  return_ [^flags, ^{value}] |.
Defined. 

#[private, pure]
Ursus Definition _generateId : UExpression ( uint64) false .
    :://  return_ ((uint64(now) << #{32}) \ (tx->timestamp & #{0xFFFFFFFF})) |.
Defined. 

#[private, pure]
Ursus Definition _incMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
    :://  return_ (#mask + (#{1} << (#{8} * uint256(#{index})))) |.
Defined. 

#[private, pure]
Ursus Definition _getMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
    :://  return_ (((#mask >> (#{8} * uint256(#{index}))) & #{0xFF})) |.
Defined. 

#[public, nonpayable]
Ursus Definition submitTransaction (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  TvmCell) (stateInit :  optional  ( TvmCell )): UExpression ( uint64) true .
    ?::// new 'senderKey :  uint256  := msg->pubkey();_|.
    ?::// new 'index :  uint8  := _findCustodian(^senderKey);_|.
    :://  _removeExpiredTransactions( ) .
    :://  require_((_getMaskValue(m_requestsMask, ^{index}) < MAX_QUEUED_REQUESTS), #{113}) .
    :://  tvm->accept() .
    :://  new ('flags: uint8 , 'realValue: uint128 ) @ (  "flags" ,  "realValue" )  := _getSendFlags(#{value}, #{allBalance}) ;_|.
    :://  m_requestsMask := _incMaskValue(m_requestsMask, ^{index}) .
    ?::// new 'trId :  uint64  := _generateId( );_|.
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
    :://  _confirmTransaction(^txn, ^{index}) .
    :://  return_ ^trId |.
Defined. 

#[public, view]
Ursus Definition sendTransaction (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint8) (payload :  TvmCell): UExpression PhantomType true .
    :://  require_((m_custodianCount == uint8(#{1})), #{108}) .
    :://  require_((msg->pubkey() == m_ownerKey), #{100}) .
    :://  tvm->accept() .
    :://  tvm->transfer(#dest, #{value}, #bounce, (uint16(#{flags}) \ FLAG_IGNORE_ERRORS), #payload) .
    :://  return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _isSubmitted (mask :  uint32) (custodianIndex :  uint8): UExpression ( boolean) false .
    :://  return_ _checkBit(#mask, #custodianIndex) |.
Defined. 


#[private, nonpayable]
Ursus Definition _initialize (ownersOpt :  optional  ( uint256[] )) (reqConfirmsOpt :  optional  ( uint8 )) (lifetimeOpt :  optional  ( uint32 )): UExpression PhantomType true .
    :://  if ( #ownersOpt->hasValue() ) then { {_:UExpression _ true} } .
    {
        ?::// new 'ownerCount :  uint8  := uint8(#{0});_|.
        ?::// new 'owners : uint256[] := #{ownersOpt}->get() ;_|.
        :://  m_ownerKey := !{owners}[(#{0})]->get() ;_|.
        ?::// new 'len :  uint256  := uint256(^{owners}->length);_|.
        :://  m_custodians := #{wrap Map (Datatypes.nil)} ;_|.
        ?::// new 'i : uint256  := uint256(#{0}) ;_|.
        ::// while (((^i < ^len) && (^ownerCount < MAX_CUSTODIAN_COUNT))) do { {_:UExpression _ true} }  .
        {
            ?::// new 'key :  uint256  := (!{owners}[!{i}])->get() ;_|.
            :://  if ( ( (!) ( m_custodians->exists(^key))) ) then { {_:UExpression _ false} }  .
            {
                ::// m_custodians:= m_custodians ->set(!{key}, !{ownerCount}).
                ::// {ownerCount} ++ |.
            }
            :://i ++|.
        }
        :://  m_custodianCount := ^ownerCount  |.
    }
    :://  if ( #reqConfirmsOpt->hasValue() ) then { {_:UExpression _ true} } .
    {
        :://  m_defaultRequiredConfirmations := math->min(m_custodianCount, #reqConfirmsOpt->get())  |.
    }
    :://  if ( #lifetimeOpt->hasValue() ) then { {_:UExpression _ true} } .
    {
        ?::// new 'newLifetime :  uint32  := #lifetimeOpt->get();_|.
        :://  if ( (^newLifetime == uint32(#{0})) ) then { {_:UExpression _ false} } else { {_:UExpression _ false} } .
        {
            :://  newLifetime := DEFAULT_LIFETIME  |.
        }
        {
            :://  newLifetime := math->max((uint32(m_custodianCount) * MIN_LIFETIME), math->min(^newLifetime, uint32((now & #{0xFFFFFFFF}))))  |.
        }
        :://  m_lifetime := ^newLifetime  |.
    }
    :://  return_ {} |.
Defined. 

#[public, nonpayable]
Ursus Definition constructor (owners :  uint256[]) (reqConfirms :  uint8) (lifetime :  uint32): UExpression PhantomType true .
    :://  require_(((uint8(#owners->length) > uint8(#{0})) && (uint8(#owners->length) <= MAX_CUSTODIAN_COUNT)), #{117}) .
    :://  if ( (msg->sender->value == uint256(#{0})) ) then { {_:UExpression _ true} } else { {_:UExpression _ true} } .
    {
        :://  require_((msg->pubkey() == tvm->pubkey()), #{100})  |.
    }
    {
        :://  require_((#owners->length == #{1}), #{126}) .
        
        :://  require_(( (#owners[#{0}]->get_default())== uint256(tvm->pubkey())), #{127})  |.
    }
    :://  tvm->accept() .
    :://  _initialize(some(#owners), some(#reqConfirms), some(#lifetime)) .
    :://  return_ {} |.
Defined. 
EndContract Implements (*интерфейсы*) .