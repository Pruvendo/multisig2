(*/Users/petrlarockin/Downloads/TON/solidity-coq-translator/ref*)
Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String.
Require Import Setoid. 
Require Import ZArith.
Require Import QArith.
Require Import Coq.Program.Equality.
Require Import Lia.

Require Import FinProof.All.
Require Import UMLang.All.
Require Import UrsusStdLib.Solidity.stdNotationsNew.
Require Import UrsusStdLib.Solidity.All.
Require Import UrsusStdLib.Solidity.unitsNotations.
Require Import UrsusStdLib.Solidity.uintCasting.
Require Import UrsusTVM.Solidity.All.
Require Import UrsusContractCreator.UrsusDefinitions.
Require Import UrsusContractCreator.ReverseTranslatorConstructions.

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
   Transaction_ι_bounce :  boolean
}
Record UpdateRequest := {
   Transaction_ι_bounce_ι_id :  uint64;
   Transaction_ι_bounce_ι_index :  uint8;
   Transaction_ι_bounce_ι_signs :  uint8;
   Transaction_ι_bounce_ι_confirmationsMask :  uint32;
   Transaction_ι_bounce_ι_creator :  uint256;
   Transaction_ι_bounce_ι_codeHash :  uint256;
   Transaction_ι_bounce_ι_custodians :  uint256;
   Transaction_ι_bounce_ι_reqConfirms :  uint8
}
Record CustodianInfo := {
   CustodianInfo_ι_index :  uint8;
   CustodianInfo_ι_pubkey :  uint256
};
Constants 
Definition FLAG_SEND_ALL_REMAINING : uint8 := Build_XUBInteger(128)
Definition FLAG_IGNORE_ERRORS : uint8 := Build_XUBInteger (2)
Definition FLAG_PAY_FWD_FEE_FROM_BALANCE : uint8 := Build_XUBInteger (1)
Definition MAX_CLEANUP_TXNS : uint256 := Build_XUBInteger (40)
Definition MAX_CUSTODIAN_COUNT : uint8 := Build_XUBInteger (32)
Definition EXPIRATION_TIME : uint64 := Build_XUBInteger (3600)
Definition MAX_QUEUED_REQUESTS : uint8 := Build_XUBInteger (5);
Record Contract := {
   #[static] botch: uint256;
   #[static] botch2: uint256;
    m_ownerKey: uint256;
    m_requestsMask: uint256;
    m_transactions: mapping  ( uint64 )(( _ResolveName "TransactionLRecord") );
    m_custodians: mapping  ( uint256 )( uint8 );
    m_custodianCount: uint8;
    m_updateRequests: mapping  ( uint64 )(( _ResolveName "UpdateRequestLRecord") );
    m_updateRequestsMask: uint32;
    m_requiredVotes: uint8;
    m_defaultRequiredConfirmations: uint8
}.
UseLocal Definition _ := [
     optional  (tuple ( uint64)( UpdateRequestLRecord ) );
     boolean;
     uint64;
    UpdateRequestLRecord;
     optional  (UpdateRequestLRecord );
     uint8;
     uint256;
    TransactionLRecord;
     optional  (TransactionLRecord );
     optional  (tuple ( uint64)( TransactionLRecord ) );
     uint128;
     optional  ( uint8 )
].
#[private, nonpayable]
Ursus Definition _deleteUpdateRequest (updateId :  uint64) (index :  uint8): UExpression PhantomType false .
   ::// m_updateRequestsMask &= ~ (uint32((#{1})) << #{index})  .
   ::// m_updateRequests[#{updateId}]->delete .
   :://return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _getExpirationBound : UExpression ( uint64) false .
   :://return_ ((uint64(now) - EXPIRATION_TIME) << ((#{32}))) |.
Defined. 

#[private, nonpayable]
Ursus Definition _removeExpiredUpdateRequests : UExpression PhantomType true .
   ::// new 'marker : (  uint64 ) @ "marker"  := _getExpirationBound ( ) ;_|.
   ::// if ( m_updateRequests->empty() ) then { {_:UExpression _ true} } .   
      :://exit_ {} .
      :://new ('updateId , 'req ) @ (  uint64 , MultisigWallet_ι_UpdateRequestLRecord )  := m_updateRequests->min() ->get() .
   :// new 'needCleanup : (  boolean ) @ "needCleanup"  := (!{updateId} <= !{marker}) .
   :// if ( !{needCleanup} ) then { {_:UExpression _ false} } .
   ://tvm->accept() .
   ://while (!{needCleanup}) do 
{
_deleteUpdateRequest(!{updateId}, !{req}->index);
 new 'reqOpt : (  optional  (tuple ( uint64)( MultisigWallet_ι_UpdateRequestLRecord ) ) ) @ "reqOpt"  := m_updateRequests->next(!{updateId});
if ( !{reqOpt}->hasValue() ) then { {_:UExpression _ false} } else { {_:UExpression _ false} } 
   ://[ !{updateId}, !{req} ] := !{reqOpt}->get() .
   ://!{needCleanup} := (!{updateId} <= !{marker})  |.

   ://!{needCleanup} := FALSE  |.


} .
   ://tvm->commit  |.

   ://return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _setConfirmed (mask :  uint32) (custodianIndex :  uint8): UExpression ( uint32) false .
   ://#{mask} |= (uint32((β #{1})) << #{custodianIndex}) .
   ://return_ #{mask} |.
Defined. 

#[private, nonpayable]
Ursus Definition _confirmUpdate (updateId :  uint64) (custodianIndex :  uint8): UExpression PhantomType false .
   :// new 'request : ( MultisigWallet_ι_UpdateRequestLRecord ) @ "request"  := m_updateRequests[#{updateId}] .
   ://!{request}->signs ++ .
   ://!{request}->confirmationsMask := _setConfirmed(!{request}->confirmationsMask, #{custodianIndex}) .
   ://m_updateRequests[#{updateId}] := !{request} .
   ://return_ {} |.
Defined. 

#[private, nonpayable]
Ursus Definition _initialize (owners :  uint256[]) (reqConfirms :  uint8): UExpression PhantomType false .
   :// new 'ownerCount : (  uint8 ) @ "ownerCount"  := (β #{0}) .
   ://m_ownerKey := #{owners}[(β #{0})] .
   :// new 'len : (  uint256 ) @ "len"  := #{owners}->length .
   :// new 'i : (  uint256 ) @ "i"  := (β #{0}) .
  refine {{ while (*actually 'for'*)((!{i} < !{len}) && (!{ownerCount} < MAX_CUSTODIAN_COUNT))do 
{
   :// new 'key : (  uint256 ) @ "key"  := #{owners}[!{i}] .
   :// if ( (~ ( m_custodians->exists(!{key}))) ) then { {_:UExpression _ false} }  |.
   ://m_custodians[!{key}] := !{ownerCount} ++  |.


   ://!{i} ++ .
} .
   ://m_defaultRequiredConfirmations := if(!{ownerCount} <= #{reqConfirms})
then!{ownerCount}
else
#{reqConfirms} .
   ://m_requiredVotes := if(!{ownerCount} <= (β #{2}))
then!{ownerCount}
else
(((!{ownerCount} * (β #{2})) + (β #{1})) / (β #{3})) .
   ://m_custodianCount := !{ownerCount} .
   ://return_ {} |.
Defined. 

#[private, nonpayable]
Ursus Definition onCodeUpgrade (newOwners :  uint256[]) (reqConfirms :  uint8): UExpression PhantomType false .
   ://tvm->resetStorage() .
   ://_initialize(#{newOwners}, #{reqConfirms}) .
   ://return_ {} |.
Defined. 

#[public, view]
Ursus Definition getUpdateRequests : UExpression (MultisigWallet_ι_UpdateRequest[]LRecord) false .
   :// new 'bound : (  uint64 ) @ "bound"  := _getExpirationBound() .

   :// if ( (!{updateId} > !{bound}) ) then { {_:UExpression _ false} }  |.
   ://updates->push(!{req})  |.

   ://new ('updateId , 'req ) @ (  uint64 , MultisigWallet_ι_UpdateRequestLRecord )   |.m_updateRequests
Defined. 

#[public, nonpayable]
Ursus Definition executeUpdate (updateId :  uint64) (code :  TvmCell): UExpression PhantomType true .
   ://require_(m_custodians->exists(msg->pubkey()), (β #{100})) .
   ://_removeExpiredUpdateRequests() .
   :// new 'requestOpt : (  optional  (MultisigWallet_ι_UpdateRequestLRecord ) ) @ "requestOpt"  := m_updateRequests->fetch(#{updateId}) .
   ://require_(!{requestOpt}->hasValue(), (β #{115})) .
   :// new 'request : ( MultisigWallet_ι_UpdateRequestLRecord ) @ "request"  := !{requestOpt}->get() .
   ://require_((tvm->hash(#{code})  == !{request}->codeHash), (β #{119})) .
   ://require_((!{request}->signs >= m_requiredVotes), (β #{120})) .
   ://tvm->accept() .
   ://_deleteUpdateRequest(#{updateId}, !{request}->index) .
   ://tvm->setcode(#{code})  .
   ://tvm->setCurrentCode(#{code})  .
   ://onCodeUpgrade(!{request}->custodians, !{request}->reqConfirms) .
   ://return_ {} |.
Defined. 

#[private, view]
Ursus Definition _findCustodian (senderKey :  uint256): UExpression ( uint8) true .
   :// new 'custodianIndex : (  optional  ( uint8 ) ) @ "custodianIndex"  := m_custodians->fetch(#{senderKey}) .
   ://require_(!{custodianIndex}->hasValue(), (β #{100})) .
   ://return_ !{custodianIndex}->get() |.
Defined. 

#[private, pure]
Ursus Definition _checkBit (mask :  uint32) (index :  uint8): UExpression ( boolean) false .
   ://return_ ((#{mask} & (uint32((β #{1})) << #{index})) != (β #{0})) |.
Defined. 

#[private, pure]
Ursus Definition _isConfirmed (mask :  uint32) (custodianIndex :  uint8): UExpression ( boolean) false .
   ://return_ _checkBit(#{mask}, #{custodianIndex}) |.
Defined. 

#[public, nonpayable]
Ursus Definition confirmUpdate (updateId :  uint64): UExpression PhantomType true .
   :// new 'index : (  uint8 ) @ "index"  := _findCustodian(msg->pubkey()) .
   ://_removeExpiredUpdateRequests() .
   :// new 'requestOpt : (  optional  (MultisigWallet_ι_UpdateRequestLRecord ) ) @ "requestOpt"  := m_updateRequests->fetch(#{updateId}) .
   ://require_(!{requestOpt}->hasValue(), (β #{115})) .
   ://require_((~ ( _isConfirmed(!{requestOpt}->get()->confirmationsMask, !{index}))), (β #{116})) .
   ://tvm->accept() .
   ://_confirmUpdate(#{updateId}, !{index}) .
   ://return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _generateId : UExpression ( uint64) false .
   ://return_ ((uint64(now) << (β #{32})) | (tx->timestamp & (β #{0xFFFFFFFF}))) |.
Defined. 

#[private, pure]
Ursus Definition _setSubmitted (mask :  uint32) (custodianIndex :  uint8): UExpression ( uint32) false .
   ://return_ _setConfirmed(#{mask}, #{custodianIndex}) |.
Defined. 

#[private, pure]
Ursus Definition _isSubmitted (mask :  uint32) (custodianIndex :  uint8): UExpression ( boolean) false .
   ://return_ _checkBit(#{mask}, #{custodianIndex}) |.
Defined. 

#[public, nonpayable]
Ursus Definition submitUpdate (codeHash :  uint256) (owners :  uint256[]) (reqConfirms :  uint8): UExpression ( uint64) true .
   :// new 'sender : (  uint256 ) @ "sender"  := msg->pubkey() .
   :// new 'index : (  uint8 ) @ "index"  := _findCustodian(!{sender}) .
   ://require_(((#{owners}->length > (β #{0})) && (#{owners}->length <= MAX_CUSTODIAN_COUNT)), (β #{117})) .
   ://_removeExpiredUpdateRequests() .
   ://require_((~ ( _isSubmitted(m_updateRequestsMask, !{index}))), (β #{113})) .
   ://tvm->accept() .
   ://m_updateRequestsMask := _setSubmitted(m_updateRequestsMask, !{index}) .
   ://updateId := _generateId() .
   ://m_updateRequests[updateId] := UpdateRequest(updateId, !{index}, (β #{0}), (β #{0}), !{sender}, #{codeHash}, #{owners}, #{reqConfirms}) .
   ://_confirmUpdate(updateId, !{index})  |.
Defined. 

#[public, view]
Ursus Definition getCustodians : UExpression (MultisigWallet_ι_CustodianInfo[]LRecord) false .

   ://custodians->push(CustodianInfo(!{index}, !{key}))  |.
   ://new ('key , 'index ) @ (  uint256 ,  uint8 )   |.m_custodians
Defined. 

#[public, view]
Ursus Definition getTransactionIds : UExpression ( uint64[]) false .

   ://ids->push(!{trId})  |.
   ://new ('trId , ' ) @ (  uint64 ,  )   |.m_transactions
Defined. 

#[public, view]
Ursus Definition getTransactions : UExpression (MultisigWallet_ι_Transaction[]LRecord) false .
   :// new 'bound : (  uint64 ) @ "bound"  := _getExpirationBound() .

   :// if ( (!{id} > !{bound}) ) then { {_:UExpression _ false} }  |.
   ://transactions->push(!{txn})  |.

   ://new ('id , 'txn ) @ (  uint64 , MultisigWallet_ι_TransactionLRecord )   |.m_transactions
Defined. 

#[public, view]
Ursus Definition getTransaction (transactionId :  uint64): UExpression (MultisigWallet_ι_TransactionLRecord) true .
   :// new 'txnOpt : (  optional  (MultisigWallet_ι_TransactionLRecord ) ) @ "txnOpt"  := m_transactions->fetch(#{transactionId}) .
   ://require_(!{txnOpt}->hasValue(), (β #{102})) .
   ://trans := !{txnOpt}->get()  |.
Defined. 

#[public, view]
Ursus Definition getParameters : UExpression ( uint8 #  uint8 #  uint64 #  uint128 #  uint8 #  uint8) false .
   ://maxQueuedTransactions := MAX_QUEUED_REQUESTS .
   ://maxCustodianCount := MAX_CUSTODIAN_COUNT .
   ://expirationTime := EXPIRATION_TIME .
   ://minValue := (β #{0}) .
   ://requiredTxnConfirms := m_defaultRequiredConfirmations .
   ://requiredUpdConfirms := m_requiredVotes  |.
Defined. 

#[public, pure]
Ursus Definition isConfirmed (mask :  uint32) (index :  uint8): UExpression ( boolean) false .
   ://confirmed := _isConfirmed(#{mask}, #{index})  |.
Defined. 

#[private, pure]
Ursus Definition _decMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
   ://return_ (#{mask} - ((β #{1}) << ((β #{8}) * uint256(#{index})))) |.
Defined. 

#[private, nonpayable]
Ursus Definition _removeExpiredTransactions : UExpression PhantomType false .
   :// new 'marker : (  uint64 ) @ "marker"  := _getExpirationBound() .
   :// if ( m_transactions->empty ) then { {_:UExpression _ false} } .   ://exit_ {} .
   ://new ('trId , 'txn ) @ (  uint64 , MultisigWallet_ι_TransactionLRecord )  := m_transactions->min() ->get() .
   :// new 'needCleanup : (  boolean ) @ "needCleanup"  := (!{trId} <= !{marker}) .
   :// if ( !{needCleanup} ) then { {_:UExpression _ false} } .
   ://tvm->accept() .
   :// new 'i : (  uint256 ) @ "i"  := (β #{0}) .
   ://while ((!{needCleanup} && (!{i} < MAX_CLEANUP_TXNS))) do 
{
!{i} ++;
m_requestsMask := _decMaskValue(m_requestsMask, !{txn}->index);
m_transactions[!{trId}] delete;
 new 'nextTxn : (  optional  (tuple ( uint64)( MultisigWallet_ι_TransactionLRecord ) ) ) @ "nextTxn"  := m_transactions->next(!{trId});
if ( !{nextTxn}->hasValue() ) then { {_:UExpression _ false} } else { {_:UExpression _ false} } 
   ://[ !{trId},  ] := !{nextTxn}->get() .
   ://!{needCleanup} := (!{trId} <= !{marker})  |.

   ://!{needCleanup} := FALSE  |.


} .
   ://tvm->commit  |.

   ://return_ {} |.
Defined. 

#[private, nonpayable]
Ursus Definition _confirmTransaction (transactionId :  uint64) (txn : MultisigWallet_ι_TransactionLRecord) (custodianIndex :  uint8): UExpression PhantomType false .
   ://if ( ((#{txn}->signsReceived + (β #{1})) >= #{txn}->signsRequired) ) then { {_:UExpression _ false} } else { {_:UExpression _ false} }  |.
   ://tvm->transfer(#{txn}->dest, #{txn}->value, #{txn}->bounce, #{txn}->sendFlags, #{txn}->payload) .
   ://m_requestsMask := _decMaskValue(m_requestsMask, #{txn}->index) .
   ://m_transactions[#{transactionId}] delete  |.

   ://#{txn}->confirmationsMask := _setConfirmed(#{txn}->confirmationsMask, #{custodianIndex}) .
   ://#{txn}->signsReceived ++ .
   ://m_transactions[#{transactionId}] := #{txn}  |.

   ://return_ {} |.
Defined. 

#[public, nonpayable]
Ursus Definition confirmTransaction (transactionId :  uint64): UExpression PhantomType true .
   :// new 'index : (  uint8 ) @ "index"  := _findCustodian(msg->pubkey()) .
   ://_removeExpiredTransactions() .
   :// new 'txnOpt : (  optional  (MultisigWallet_ι_TransactionLRecord ) ) @ "txnOpt"  := m_transactions->fetch(#{transactionId}) .
   ://require_(!{txnOpt}->hasValue(), (β #{102})) .
   :// new 'txn : ( MultisigWallet_ι_TransactionLRecord ) @ "txn"  := !{txnOpt}->get() .
   ://require_((~ ( _isConfirmed(!{txn}->confirmationsMask, !{index}))), (β #{103})) .
   ://tvm->accept() .
   ://_confirmTransaction(#{transactionId}, !{txn}, !{index}) .
   ://return_ {} |.
Defined. 

#[private, pure]
Ursus Definition _getSendFlags (value :  uint128) (allBalance :  boolean): UExpression ( uint8 #  uint128) false .
   :// new 'flags : (  uint8 ) @ "flags"  := (FLAG_IGNORE_ERRORS | FLAG_PAY_FWD_FEE_FROM_BALANCE) .
   :// if ( #{allBalance} ) then { {_:UExpression _ false} } .
   ://!{flags} := (FLAG_IGNORE_ERRORS | FLAG_SEND_ALL_REMAINING) .
   ://#{value} := (β #{0})  |.

   ://return_ [ !{flags}, #{value} ] |.
Defined. 

#[private, pure]
Ursus Definition _incMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
   ://return_ (#{mask} + ((β #{1}) << ((β #{8}) * uint256(#{index})))) |.
Defined. 

#[private, pure]
Ursus Definition _getMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint8) false .
   ://return_ uint8(((#{mask} >> ((β #{8}) * uint256(#{index}))) & (β #{0xFF}))) |.
Defined. 

#[public, nonpayable]
Ursus Definition submitTransaction (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  TvmCell): UExpression ( uint64) true .
   :// new 'senderKey : (  uint256 ) @ "senderKey"  := msg->pubkey() .
   :// new 'index : (  uint8 ) @ "index"  := _findCustodian(!{senderKey}) .
   ://_removeExpiredTransactions() .
   ://require_((_getMaskValue(m_requestsMask, !{index}) < MAX_QUEUED_REQUESTS), (β #{113})) .
   ://tvm->accept() .
   ://new ('flags , 'realValue ) @ (  uint8 ,  uint128 )  := _getSendFlags(#{value}, #{allBalance}) .
   :// new 'requiredSigns : (  uint8 ) @ "requiredSigns"  := m_defaultRequiredConfirmations .
   ://if ( (!{requiredSigns} <= (β #{1})) ) then { {_:UExpression _ false} } else { {_:UExpression _ false} } .
   ://tvm->transfer(#{dest}, !{realValue}, #{bounce}, !{flags}, #{payload}) .
   ://return_ (β #{0}) |.

   ://m_requestsMask := _incMaskValue(m_requestsMask, !{index}) .
   :// new 'trId : (  uint64 ) @ "trId"  := _generateId() .
   :// new 'txn : ( MultisigWallet_ι_TransactionLRecord ) @ "txn"  := Transaction(!{trId}, (β #{0}), !{requiredSigns}, (β #{0}), !{senderKey}, !{index}, #{dest}, !{realValue}, !{flags}, #{payload}, #{bounce}) .
   ://_confirmTransaction(!{trId}, !{txn}, !{index}) .
   ://return_ !{trId} |.

Defined. 

#[public, view]
Ursus Definition sendTransaction (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint8) (payload :  TvmCell): UExpression PhantomType true .
   ://require_((m_custodianCount == (β #{1})), (β #{108})) .
   ://require_((msg->pubkey() == m_ownerKey), (β #{100})) .
   ://tvm->accept() .
   ://tvm->transfer(#{dest}, #{value}, #{bounce}, (#{flags} | FLAG_IGNORE_ERRORS), #{payload}) .
   ://return_ {} |.
Defined. 

#[public, nonpayable]
Ursus Definition constructor (owners :  uint256[]) (reqConfirms :  uint8): UExpression PhantomType true .
   ://require_((msg->pubkey() == tvm->pubkey()), (β #{100})) .
   ://require_(((#{owners}->length > (β #{0})) && (#{owners}->length <= MAX_CUSTODIAN_COUNT)), (β #{117})) .
   ://tvm->accept() .
   ://_initialize(#{owners}, #{reqConfirms}) .
   ://return_ {} |.
Defined. 
EndContract Implements (*интерфейсы*) .