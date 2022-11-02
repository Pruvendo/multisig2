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
  UpdateRequest_ι_custodians :  optional  ( uint256[] );
  UpdateRequest_ι_reqConfirms :  optional  ( uint8 );
  UpdateRequest_ι_lifetime :  optional  ( uint32 )
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
    m_ownerKey: uint256;
    m_requestsMask: uint256;
    m_transactions: mapping  ( uint64 )((_ResolveName "Transaction") );
    m_custodians: mapping  ( uint256 )( uint8 );
    m_custodianCount: uint8;
    m_updateRequests: mapping  ( uint64 )((_ResolveName "UpdateRequest") );
    m_updateRequestsMask: uint32;
    m_requiredVotes: uint8;
    m_defaultRequiredConfirmations: uint8;
    m_lifetime: uint32
}.
UseLocal Definition _ := [
     optional  (tuple ( uint64)( (UpdateRequestLRecord) ) );
     boolean;
     uint64;
    (UpdateRequestLRecord);
     uint8;
     uint32;
     slice_;
     optional  ( uint256[] );
     builder_;
     TvmCell;
     optional  ((UpdateRequestLRecord) );
     uint256;
    (TransactionLRecord);
     optional  ((TransactionLRecord) );
     optional  (tuple ( uint64)( (TransactionLRecord) ) );
     uint128;
     optional  ( uint8 );
     uint256[];

     UpdateRequestLRecord[];
     (* temporary *) optional TvmBuilder;
     CustodianInfoLRecord [];
     TransactionLRecord [];
     address;
     optional ( TvmCell );
     optional ( uint256 );
     optional ( uint256[] ); 
     optional ( uint8 ); 
     optional ( uint32 );

     optional
     (bool **
      tvmTypes.TvmSlice);
    optional ((uint256) [] ** tvmTypes.TvmSlice);
    optional
     ((mapping uint256 uint8 * (uint8 * uint256)) ** tvmTypes.TvmSlice);
    mapping uint256 uint8 ** (uint8 ** uint256);
    optional
     ((uint8 * uint32) **
      tvmTypes.TvmSlice);
    uint8 ** uint32
].

Local Open Scope ursus_scope_UpdateRequest.
Local Open Scope ursus_scope_CustodianInfo.
Local Open Scope ursus_scope_Transaction.





(* ********************************** move me  ************************************* *)
Definition URValue' b X := (URValue X b).
Definition URValue'_false := fun X => URValue X false.
Print ULValueL.

Definition ULValueL' := fun Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X  => 
          @ULValueL (* boolean XUInteger optional tuple mapping *) Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X.
Definition URValueL'_false := fun Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X  => 
          @URValueL (* boolean XUInteger optional tuple mapping *) Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X false.

Notation ULValueL'' := (ULValueL' _ _ _ _ _ _ _ _).
Notation URValueL'' := (URValueL'_false _ _ _ _ _ _ _ _).
Check ULValueL''.
Check URValueL''.

(* fun (x₁:T₁)..(xₙ:Tₙ) => D t₁..tₘ *)
(* Print ULValueL. *)

Identity Coercion aaa: URValueL'_false >-> URValueL.
Identity Coercion bbb: ULValueL' >-> ULValueL. 

(* Variable f :> forall Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X  
          (x: ULValueL' Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X), 
          URValueL'_false Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X.  *) 

Definition ULtoRValue' : forall Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X  
          (x: ULValueL' Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X), 
          URValueL'_false Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X.
    intros.
    refine (ULtoRValue x).
Defined.

About URValueP.

Definition ULtoRValue'' : forall Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X  
          (x: @ULValueL Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X), 
          @URValueP boolean XUInteger optional tuple mapping Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC X false.
    intros.
    refine (ULtoRValue x).
Defined.

Coercion ULtoRValue' : ULValueL' >-> URValueL'_false.
Coercion ULtoRValue'' : ULValueL >-> URValueP.

Notation URValue_false X := (URValue X false).
(* Notation ULValue' X := (ULValue X). *)
Definition IdType (X: Type)  := X.
(* Definition sRInject' {X} (x:X): URValue_false X := sRInject _ _ _ _ x. *)
(* Print URValue. *)
Definition sRInject'' (* Ledger LedgerMainState LedgerLocalState LedgerVMState
          LedgerMessagesAndEvents GlobalParams OutgoingMessageParams LC *) (X:Type) (x: IdType X): 
          URValueL'_false LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord
          MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord LedgerLLedgerClass X.
      intros.
      :: (sRInject _ _ _ _ x).
      Defined. 
(* Definition ULtoRValue' (X:Type) (x: ULValue X): URValue_false X := ULtoRValue x. *)
(* Variable ULtoRValue'' :> forall (X:Type) (x: ULValue X), URValue_false X. *)

Notation N' := (IdType N).
Definition N2N' (a:N):N' := a.

Coercion N2N': N >-> N'.
Coercion sRInject'': IdType >-> URValueL'_false.

Check (_: ULValueL'' _): URValueL'' _.
(* ********************************** move me  ************************************* *)











#[private, nonpayable]
Ursus Definition _deleteUpdateRequest (updateId :  uint64) (index :  uint8): UExpression PhantomType false .
{
    :://  m_updateRequestsMask &= ( ~ ( (uint32(1) << {index}))) .
    :://  m_updateRequests[updateId] ->delete  |.
}
return.
Defined.
Sync.

#[private, view]
Ursus Definition _getExpirationBound : UExpression ( uint64) false .
{ :://  return_  {} |. }
return || ((uint64(now) - uint64(m_lifetime)) << {32}) ||.
Defined.
Sync.

#[private, nonpayable]
Ursus Definition _removeExpiredUpdateRequests : UExpression PhantomType true .
{
    ?::// new 'marker :  uint64  := _getExpirationBound( );_|.
    :://  if ( m_updateRequests->empty() ) then { {_:UExpression _ true} } .
    {
        :://  exit_ {} |.
    }
    ?::// new ('updateId : uint64, 'req : UpdateRequestLRecord ) @ ( _ , "req" )  := m_updateRequests->min()->get() ; _| . 
    ?::// new 'needCleanup :  boolean  := (updateId <= marker);_|.
    :://  if ( needCleanup ) then { {_:UExpression _ true} }  |.
    {
        :://  tvm->accept() .
        :://  while (needCleanup) do { {_:UExpression _  true} }  ;_|.
            :://  _deleteUpdateRequest(updateId, ({req} -> UpdateRequest_ι_index)) .
            ?::// new 'reqOpt :  optional (tuple ( uint64)( UpdateRequestLRecord ))   := m_updateRequests->next(updateId);_|.
            :://  if ( reqOpt->hasValue() ) then { {_:UExpression _ true} } else { {_:UExpression _ false} }  |.
            {
                :://  [updateId, req] := reqOpt->get() .
                :://  needCleanup := (updateId <= marker)  |.
            }
            {
                :://  needCleanup := @false  |.
            }
        :://  tvm->commit()  |.
    }
}
return.
Defined.
Sync.

#[private, pure]
Ursus Definition _setConfirmed (mask :  uint32) (custodianIndex :  uint8): UExpression ( uint32) false .
{
    :://  {mask} |= (uint32(#{1}) << {custodianIndex}) |.
}
    return || {mask} ||.

Defined.
Sync.

#[private, nonpayable]
Ursus Definition _confirmUpdate (updateId :  uint64) (custodianIndex :  uint8): UExpression PhantomType false .
{
    ?::// new 'request : (UpdateRequestLRecord)  := m_updateRequests[{updateId}];_|.
    :://  request->UpdateRequest_ι_signs ++ .
    :://  request->UpdateRequest_ι_confirmationsMask := _setConfirmed(request->UpdateRequest_ι_confirmationsMask, {custodianIndex}) .
    :://  m_updateRequests := m_updateRequests->set(updateId, request) |.
}
return.
Defined.
Sync.
Context `{boolFunRec_gen (uint256) []}.
#[private, nonpayable]
Ursus Definition _initialize (ownersOpt :  optional  ( uint256[] )) (reqConfirms :  uint8) (lifetime :  uint32): UExpression PhantomType true .
{
    :://  if ( {ownersOpt}->hasValue() ) then { {_:UExpression _ true} } .
    {
        ?::// new 'ownerCount :  uint8  := uint8(#{0});_|.
        ?::// new 'owners :  uint256[]  := {ownersOpt}->get();_|.
        :://  if ( (owners->length == #{0}) ) then { {_:UExpression _ false} } .
        {
            :://  owners->push(tvm->pubkey())  |.
        }
        :://  m_ownerKey := !{owners}[(#{0})]->get() ;_|.
        ?::// new 'len :  uint256  := uint256(owners->length);_|.
        :://  m_custodians := #{wrap Map (Datatypes.nil)} ;_|.
        ?::// new 'i : uint256  := uint256(#{0}) ;_|.
        ::// while (((i < len) && (ownerCount < MAX_CUSTODIAN_COUNT))) do { {_:UExpression _ true} }  .
        {
            ?::// new 'key :  uint256  := (owners[i])->get() ;_|.
            :://  if ( ( ! ( m_custodians->exists(key))) ) then { {_:UExpression _ false} }  .
            {
                ::// m_custodians:= m_custodians ->set(key, ownerCount).
                ::// ownerCount++ |.
            }
            :://  i ++|.
        }
        :://  m_custodianCount := ownerCount  |.
    }
    :://  m_defaultRequiredConfirmations := math->min(m_custodianCount, {reqConfirms}) .
    :://  m_requiredVotes := (m_custodianCount <= uint8(#{2})) ? m_custodianCount : (((m_custodianCount * #{2}) + #{1}) / #{3}) .
    ?::// new 'minLifetime :  uint32  := (uint32(m_custodianCount) * uint32(MIN_LIFETIME));_|.
    :://  if ( ({lifetime} == uint32(#{0})) ) then { {_:UExpression _ false} } else { {_:UExpression _ false} }  |.
    {
        :://  m_lifetime := DEFAULT_LIFETIME  |.
    }
    {
        :://  m_lifetime := math->max(minLifetime, math->min({lifetime}, uint32((now & #{0xFFFFFFFF}))))  |.
    }
}
return.
Defined.
Sync.


#[private, nonpayable]
Ursus Definition onCodeUpgrade (data :  TvmCell): UExpression PhantomType true .
{
    :://  tvm->resetStorage() .
    ?::// new 'owners :  optional  (listArray uint256) := {} ;_|.
    ::// new 'slice :  TvmSlice @ "slice"  := (^{data}->toSlice());_|.
    ::// new 'ownersAsArray :  boolean @  "ownersAsArray" :=  slice->decode(bool);_|.
    :://  if ( ownersAsArray ) then { {_:UExpression _ true} } else { {_:UExpression _ true} } .
    {
        :://  owners ->set (slice->decode(uint256[]))  |.
    }
    {
        (* Locate "**". *)
        :://  [m_custodians, m_custodianCount, m_ownerKey] := slice->decode(mapping uint256 uint8, uint8, uint256)  |.
    }
    :://  new ('reqConfirms:  uint8 , 'lifetime:  uint32) @ ( "reqConfirms" , "lifetime" ) := slice->decode(uint8, uint32);_|.
    :://  _initialize(owners, reqConfirms, lifetime)  |.
}
return.
Defined.

Context `{ boolFunRec_gen UpdateRequestLRecord []}.
#[external, view, returns = updates]
Ursus Definition getUpdateRequests : UExpression ((UpdateRequestLRecord[])) false .
{
    ?::// new 'bound :  uint64  := _getExpirationBound( );_|.
    :://  for ( 'item : m_updateRequests ) do { {_:UExpression _ false} } |.
    {   
        ::// new ('updateId: uint64 , 'req: UpdateRequestLRecord ) @ ("updateId", "req") := item ;_|.
        :://  if ( (updateId > bound) ) then { {_:UExpression _ false} }  |.
        {
            :://  updates->push(req)  |.
        }
    }
}
return.
Defined.


#[public, nonpayable]
Ursus Definition executeUpdate (updateId :  uint64) (code : optional ( TvmCell )): UExpression PhantomType true .
{
    :://  require_(m_custodians->exists(msg->pubkey()), #{100}) .
    :://  _removeExpiredUpdateRequests( ) .
    ?::// new 'requestOpt :  optional  ((UpdateRequestLRecord) )  := m_updateRequests->fetch(updateId);_|.
    :://  require_(requestOpt->hasValue(), #{115}) .
    ?::// new 'request : (UpdateRequestLRecord)  := requestOpt->get();_|.
    (* TODO 2 *)
    :://  if ( {_ :URValue XBool _ }  ) then { {_:UExpression _ true} } else { {_:UExpression _ true} } .
        refine ||request->UpdateRequest_ι_codeHash->hasValue()||.
    {
        :://  require_({code}->hasValue(), #{119}) .
        (* TODO 2 *)
        :://  require_(({_:URValue XBool _ }), #{119})  |.
        refine ||(tvm->hash({code} ->get_default())  == request->UpdateRequest_ι_codeHash->get_default())||.
    }
    {
        :://  require_(( ! ( code->hasValue())), #{125})  |.
    }
    (* TODO 2 *)
    :://  require_({_: URValue boolean _}, #{120}) .
            refine || (request->UpdateRequest_ι_signs >= m_requiredVotes) ||.
    :://  tvm->accept() .
    :://  _deleteUpdateRequest({updateId}, request->UpdateRequest_ι_index) .
    :://  tvm->commit() .
    (* TODO 2 *)
    :://  if ( {_ :URValue XBool _ } ) then { {_:UExpression _ true} } .
        refine || request->UpdateRequest_ι_codeHash->hasValue() ||.
    {
        ?::// new 'newcode :  TvmCell @ "newcode"  := code ->get();_|.
        :://  tvm->setcode(newcode)  .
        :://  tvm->setCurrentCode(newcode)   |.
    }
    ?::// new 'data :  builder_ := {} ;_|.
    (* TODO 2 *)
    :://  if ( {_:URValue boolean _} ) then { {_:UExpression _ true} } else { {_:UExpression _ true} } .
            refine || request->UpdateRequest_ι_custodians->hasValue()||.
    {
        (* TODO 3 *)
        :://   data->store(@true (*, request->UpdateRequest_ι_custodians->get()*))  |.
    }
    {
        :://  data->store(@false, m_custodians, m_custodianCount, m_ownerKey)  |.
    }
    (* TODO 2 *)
    :://  if ({_ :URValue XBool _ }  ) then { {_:UExpression _ true} } else { {_:UExpression _ true} } .
        refine ||request->UpdateRequest_ι_reqConfirms->hasValue()||.
    {
        (* TODO 3 *)
        :://  data->store({}(*request->UpdateRequest_ι_reqConfirms->get()*))  |.
    }
    {
        :://  data->store(m_defaultRequiredConfirmations)  |.
    }
    (* TODO 2 *)
    :://  if ( {_ :URValue XBool _ }  ) then { {_:UExpression _ true} } else { {_:UExpression _ true} } .
        refine ||request->UpdateRequest_ι_lifetime->hasValue()||.
    {
        (* TODO 3 *)
        :://  data->store({} (*request->UpdateRequest_ι_lifetime->get()*))  |.
    }
    {
        :://  data->store(m_lifetime)  |.
    }
    :://  onCodeUpgrade(data->toCell())  |.
}
return.
Defined.
Sync.

#[private, view]
Ursus Definition _findCustodian (senderKey :  uint256): UExpression ( uint8) true .
{
    ?::// new 'custodianIndex :  optional  ( uint8 )  := m_custodians->fetch({senderKey});_|.
    :://  require_(custodianIndex->hasValue(), #{100}) .
    :://  return_ custodianIndex->get() |.
}
(* TODO 1 *)
return (*||custodianIndex->get()||*) .
Defined.
Sync.

#[private, pure]
Ursus Definition _checkBit (mask :  uint32) (index :  uint8): UExpression ( boolean) false .
{ :://  return_  {} |. }
return || (({mask} & (uint32(#{1}) << ^{index})) != uint32(#{0})) ||.
Defined.
Sync.

#[private, pure]
Ursus Definition _isConfirmed (mask :  uint32) (custodianIndex :  uint8): UExpression ( boolean) false .
{ :://  return_  {} |. }
return || _checkBit({mask}, {custodianIndex})||.
Defined.
Sync.

#[public, nonpayable]
Ursus Definition confirmUpdate (updateId :  uint64): UExpression PhantomType true .
{
    ?::// new 'index :  uint8  := _findCustodian(msg->pubkey());_|.
    :://  _removeExpiredUpdateRequests( ) .
    ?::// new 'requestOpt :  optional  ((UpdateRequestLRecord) )  := m_updateRequests->fetch({updateId});_|.
    :://  require_(requestOpt->hasValue(), #{115}) .
    (* TODO 2 *)
    :://  require_(( ! ({_:URValue boolean _} )), #{116}) .
        refine || _isConfirmed(requestOpt->get_default()->UpdateRequest_ι_confirmationsMask, ^{index})||.
    :://  tvm->accept() .
    :://  _confirmUpdate({updateId}, ^{index})  |.
}
return.
Defined.
Sync.

#[private, pure]
Ursus Definition _generateId : UExpression ( uint64) false .
{ :://  return_  {} |. }
return ||((uint64(now) << (#{32})) \ (tx->timestamp & #{0xFFFFFFFF})) ||.
Defined.
Sync.

#[private, pure]
Ursus Definition _isSubmitted (mask :  uint32) (custodianIndex :  uint8): UExpression ( boolean) false .
{ :://  return_  {} |. }
return || _checkBit({mask}, {custodianIndex}) ||.
Defined.
Sync.

#[public, nonpayable, returns=updateId]
Ursus Definition submitUpdate (codeHash : optional ( uint256 )) (owners : optional ( uint256[] )) (reqConfirms : optional ( uint8 )) (lifetime : optional ( uint32 )): UExpression ( uint64) true .
{
    ?::// new 'sender :  uint256  := msg->pubkey();_|.
    ?::// new 'index :  uint8  := _findCustodian(sender);_|.
    (* TODO 2 *)
    :://  if ( {_:URValue boolean _ } ) then { {_:UExpression _ true} } .
    refine ||  owners->hasValue() ||.
    {
        ?::// new 'newOwnerCount :  uint256  := uint256(owners->get()->length);_|.
        :://  require_(((newOwnerCount > uint256(#{0})) && (newOwnerCount <= MAX_CUSTODIAN_COUNT)), #{117})  |.
    }
    :://  _removeExpiredUpdateRequests( ) .
    :://  require_(( ! ( _isSubmitted(m_updateRequestsMask, ^{index}))), #{113}) .
    :://  tvm->accept() .
    :://  if ( codeHash->hasValue() ) then { {_:UExpression _ false} } .
    {
        :://  if ( (codeHash->get_default() == tvm->hash(tvm->code()) ) ) then { {_:UExpression _ false} }  |.
        {
            :://  codeHash->reset() |.
        }
    }
    :://  m_updateRequestsMask := _setConfirmed(m_updateRequestsMask, {index}) .
    ?::// new 'updateId :_  := _generateId( ) ;_|.
    
    :://m_updateRequests := m_updateRequests->set(  updateId, 
                                                    [ updateId, 
                                                      {index},
                                                      uint8(#{0}), 
                                                      uint32(#{0}),
                                                      sender,
                                                      codeHash,
                                                      owners,
                                                      reqConfirms, 
                                                      lifetime ] ) ;_| .
    :://  _confirmUpdate(updateId, {index})  |.
}
return.
Defined.
Sync.

Context `{ XDefault CustodianInfoLRecord []}.
#[external, view, returns=custodians]
Ursus Definition getCustodians : UExpression ((CustodianInfoLRecord[])) false .
{
    ::// for ( 'item : m_custodians ) do { {_:UExpression _ false} } |.
    {
        ::// new ('key: uint256 , 'index: uint8 ) @ ("key", "index") := item ;_|.
        ::// {custodians}->push([ ^{index}, ^key ])|.
    }
}
return.
Defined.
Sync.


Context `{boolFunRec_gen TransactionLRecord []}.
Context `{XDefault TransactionLRecord []}.
#[external, view, returns=transactions]
Ursus Definition getTransactions : UExpression ((TransactionLRecord[])) false .
{
    ?::// new 'bound :  uint64  := _getExpirationBound( );_|.
    ::// for ( 'item : m_transactions ) do { {_:UExpression _ false} } |.
    {
        ::// new ('id: uint64 , 'txn:  TransactionLRecord ) @ ("updateId", "req") := item ;_|. 
        :://  if ( ( {id} > bound) ) then { {_:UExpression _ false} }  |.
        {
            :://  transactions->push(txn)  |.
        }
    }
}
return.
Defined.
Sync.


Context `{XDefault TransactionLRecord}.
#[external, view, returns=trans]
Ursus Definition getTransaction (transactionId :  uint64): UExpression ((TransactionLRecord)) true .
{
    ?::// new 'txnOpt :  optional  ((TransactionLRecord) )  := m_transactions->fetch({transactionId});_|.
    :://  require_(txnOpt->hasValue(), #{102}) .
    :://  trans := txnOpt->get()  |.
}
return.
Defined.
Sync.

#[external, view]
Ursus Definition getParameters : UExpression ( uint8 **  uint8 **  uint64 **  uint128 **  uint8 **  uint8) false .
{ ::// return_ {}|. }
(* TODO 4 *)
return (*|| [  MAX_QUEUED_REQUESTS ,  MAX_CUSTODIAN_COUNT,  uint64(m_lifetime),  uint128(#{0}), m_defaultRequiredConfirmations, m_requiredVotes] ||*).
Defined.
Sync.

#[external, pure]
Ursus Definition isConfirmed (mask :  uint32) (index :  uint8): UExpression ( boolean) false .
{ ::// return_ {}|. }
return ||_isConfirmed({mask}, {index})||.
Defined.
Sync.

#[private, pure]
Ursus Definition _decMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
{ ::// return_ {}|. }
return ||  ({mask} - (#{1} << (#{8} * uint256({index})))) ||.
Defined.
Sync.

#[private, nonpayable]
Ursus Definition _removeExpiredTransactions : UExpression PhantomType true .
{
    ?::// new 'marker :  uint64  := _getExpirationBound( );_|.
    :://  if ( m_transactions->empty() ) then { {_:UExpression _ true} } .
    {
        :://  exit_ {} |.
    }
    :://  new ('trId:  uint64 , 'txn: (TransactionLRecord)) @ ("trId", "txn"):= m_transactions->min() ->get();_|.
    ?::// new 'needCleanup :  boolean  := (trId <= marker);_|.
    :://  if ( needCleanup ) then { {_:UExpression _ true} }  |.
    {
        :://  tvm->accept() .
        ?::// new 'i :  uint256  := uint256(#{0});_|.
        :://  while ((needCleanup && (i < MAX_CLEANUP_TXNS))) do { {_:UExpression _  true} }  ;_|.
            :://  i ++ .
            :://  m_requestsMask := _decMaskValue(m_requestsMask, txn->Transaction_ι_index) .
            :://  m_transactions[trId] ->delete .
            ?::// new 'nextTxn :  optional  (tuple ( uint64)( (TransactionLRecord) ) )  := m_transactions->next(trId);_|.
            :://  if ( nextTxn->hasValue() ) then { {_:UExpression _ true} } else { {_:UExpression _ false} }  |.
            {
                :://  [trId, txn] := nextTxn->get() .
                :://  needCleanup := (trId <= marker)  |.
            }
            {
                :://  needCleanup := @false  |.
            }
        :://  tvm->commit()  |.
    }
}
return.
Defined.
Sync.

#[private, nonpayable]
Ursus Definition _confirmTransaction (txn : (TransactionLRecord)) (custodianIndex :  uint8): UExpression PhantomType false .
{
    (* TODO 2 *)
    :://  if ( {_:URValue boolean false} ) 
            then { {_:UExpression _ false} } 
            else { {_:UExpression _ false} }  |.
            refine ||(({txn}->Transaction_ι_signsReceived + (#{1})) >= {txn}->Transaction_ι_signsRequired) ||.
    {
        (* TODO 2 *)
        :://  if ( {_:URValue boolean false} ) then { {_:UExpression _ false} } else { {_:UExpression _ false} } .
            refine ||{txn}->Transaction_ι_stateInit->hasValue()||.
            {
                :://  tvm->transfer(^txn->Transaction_ι_dest, 
                                    ^txn->Transaction_ι_value, 
                                    ^txn->Transaction_ι_bounce, 
                                    ^txn->Transaction_ι_sendFlags, 
                                    ^txn->Transaction_ι_payload) |.
                                    (* ^txn->Transaction_ι_stateInit->get())  |. TODO 0 *)
            }
            {
                :://  tvm->transfer(^txn->Transaction_ι_dest, 
                                    ^txn->Transaction_ι_value, 
                                    ^txn->Transaction_ι_bounce, 
                                    ^txn->Transaction_ι_sendFlags, 
                                    ^txn->Transaction_ι_payload) |.
            }
        :://  m_requestsMask := _decMaskValue(m_requestsMask, {txn}->Transaction_ι_index) .
        :://  m_transactions[{txn}->Transaction_ι_id] ->delete  |.
    }
    {
        :://  {txn}->Transaction_ι_confirmationsMask := _setConfirmed({txn}->Transaction_ι_confirmationsMask, {custodianIndex}) .
        :://  {txn}->Transaction_ι_signsReceived ++ .
        :://  m_transactions := m_transactions->set(^txn->Transaction_ι_id, ^txn)  |.
    }
}
return.
Defined.
Sync.

#[public, nonpayable]
Ursus Definition confirmTransaction (transactionId :  uint64): UExpression PhantomType true .
{
    ?::// new 'index :  uint8  := _findCustodian(msg->pubkey());_|.
    :://  _removeExpiredTransactions( ) .
    ?::// new 'txnOpt :  optional  ((TransactionLRecord) )  := m_transactions->fetch({transactionId});_|.
    :://  require_(txnOpt->hasValue(), #{102}) .
    ?::// new 'txn : (TransactionLRecord)  := txnOpt->get();_|.
    (* TODO 2 *)
    :://  require_( ! ( {_:URValue boolean false }), #{103}) .
        refine || _isConfirmed(txn->Transaction_ι_confirmationsMask, {index}) ||.
    :://  tvm->accept() .
    :://  _confirmTransaction(txn, {index})  |.
}
return.
Defined.
Sync.

#[private, pure]
Ursus Definition _getSendFlags (value :  uint128) (allBalance :  boolean): UExpression ( uint8 **  uint128) false .
{
    ?::// new 'flags :  uint8  := (FLAG_IGNORE_ERRORS \ FLAG_PAY_FWD_FEE_FROM_BALANCE);_|.
    :://  if ( {allBalance} ) then { {_:UExpression _ false} } .
    {
        :://  flags := (FLAG_IGNORE_ERRORS \ FLAG_SEND_ALL_REMAINING) .
        :://  {value} := uint128(#{0})  |.
    }
    :://  return_ [flags, {value}] |.
}
(* TODO 1 *)
return (*|| [flags, {value}] ||*).
Defined .
Sync.

#[private, pure]
Ursus Definition _incMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
{ :://  return_ {} |. }
return || ({mask} + (#{1} << (#{8} * uint256({index})))) ||.
Defined.
Sync.

#[private, pure]
Ursus Definition _getMaskValue (mask :  uint256) (index :  uint8): UExpression ( uint256) false .
{ ::// return_ {}|. }
return  ||   (uint256(((mask >> (#{8} * uint256({index}))) & #{0xFF}))) ||.
Defined.
Sync.

#[public, nonpayable]
Ursus Definition submitTransaction (dest :  address) (value :  uint128) (bounce :  boolean) (allBalance :  boolean) (payload :  TvmCell) (stateInit :  optional  ( TvmCell )): UExpression ( uint64) true .
{
    ?::// new 'senderKey :  uint256  := msg->pubkey();_|.
    ?::// new 'index :  uint8  := _findCustodian(senderKey);_|.
    :://  _removeExpiredTransactions( ) .
    :://  require_((_getMaskValue(m_requestsMask, {index}) < MAX_QUEUED_REQUESTS), #{113}) .
    :://  tvm->accept() .
    :://  new ('flags:  uint8 , 'realValue:  uint128) @ ("flags", "realValue") := _getSendFlags({value}, {allBalance});_|.
    :://  m_requestsMask := _incMaskValue(m_requestsMask, {index}) .
    ?::// new 'trId :  uint64  := _generateId( );_|.
    ?::// new 'txn :  TransactionLRecord := [!{trId}, 
                                                uint32(#{0}), 
                                                m_defaultRequiredConfirmations, 
                                                uint8(#{0}), 
                                                !{senderKey}, 
                                                !{index}, 
                                                {dest}, 
                                                !{realValue}, 
                                                uint16(!{flags}), 
                                                {payload}, 
                                                {bounce}, 
                                                {stateInit} ];_|.
    :://  _confirmTransaction( {txn}, {index}) .
    :://  return_ trId |.
}
(* TODO 1 *)
return (*|| ^{trId} ||*).
Defined.
Sync.

#[public, view]
Ursus Definition sendTransaction (dest :  address) (value :  uint128) (bounce :  boolean) (flags :  uint8) (payload :  TvmCell): UExpression PhantomType true .
{
    :://  require_((m_custodianCount == uint8(#{1})), #{108}) .
    :://  require_((msg->pubkey() == m_ownerKey), #{100}) .
    :://  tvm->accept() .
    :://  tvm->transfer( {dest}, {value}, {bounce}, (uint16({flags}) \ FLAG_IGNORE_ERRORS), {payload})  |.
}
return.
Defined.
Sync.



#[public, nonpayable]
Ursus Definition constructor (owners :  uint256[]) (reqConfirms :  uint8) (lifetime :  uint32): UExpression PhantomType true .
{
    :://  require_(((uint256({owners}->length) > uint256(#{0})) && (uint256({owners}->length) <= MAX_CUSTODIAN_COUNT)), #{117}) .
    :://  if ( (msg->sender->value == uint8(#{0})) ) then { {_:UExpression _ true} } else { {_:UExpression _ true} } .
    {
        :://  require_((msg->pubkey() == tvm->pubkey()), #{100})  |.
    }
    {
        :://  require_((uint256({owners}->length) == uint256(#{1})), #{126}) .
        :://  require_(( (owners[#{0}]->get_default())== uint256(tvm->pubkey())), #{127})  |.
    }
    :://  tvm->accept() .
    :://  _initialize(some({owners}), {reqConfirms}, {lifetime})  |.
}
return.
Defined.
Sync.
EndContract Implements (*интерфейсы*) .