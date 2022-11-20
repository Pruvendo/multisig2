


contract MultisigWallet is  {

struct Transaction {
uint64 id;
uint32 confirmationsMask;
uint8 signsRequired;
uint8 signsReceived;
uint256 creator;
uint8 index;
address dest;
uint128 value;
uint16 sendFlags;
TvmCell payload;
bool bounce;
optional (TvmCell) stateInit;

}

struct UpdateRequest {
uint64 id;
uint8 index;
uint8 signs;
uint32 confirmationsMask;
uint256 creator;
optional (uint256) codeHash;
optional (uint256[]) custodians;
optional (uint8) reqConfirms;
optional (uint32) lifetime;

}

struct CustodianInfo {
uint8 index;
uint256 pubkey;

}

uint8 constant FLAG_SEND_ALL_REMAINING = Build_XUBInteger 128;
uint8 constant FLAG_IGNORE_ERRORS = Build_XUBInteger 2;
uint8 constant FLAG_PAY_FWD_FEE_FROM_BALANCE = Build_XUBInteger 1;
uint256 constant MAX_CLEANUP_TXNS = Build_XUBInteger 40;
uint8 constant MAX_CUSTODIAN_COUNT = Build_XUBInteger 32;
uint32 constant MIN_LIFETIME = Build_XUBInteger 10;
uint32 constant DEFAULT_LIFETIME = Build_XUBInteger 3600;
uint8 constant MAX_QUEUED_REQUESTS = Build_XUBInteger 5;
uint256  m_ownerKey;
uint256  m_requestsMask;
mapping (uint64 => Transaction)  m_transactions;
mapping (uint256 => uint8)  m_custodians;
uint8  m_custodianCount;
mapping (uint64 => UpdateRequest)  m_updateRequests;
uint32  m_updateRequestsMask;
uint8  m_requiredVotes;
uint8  m_defaultRequiredConfirmations;
uint32  m_lifetime;


