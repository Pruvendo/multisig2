(*/Users/petrlarockin/Downloads/TON/solidity-coq-translator/ref*)
Require Import Enviroment.Enviroment.
Inductive LocalFields00000I := | ι000000 | ι000001 .
Definition LocalState00000L := [( XHMap (string*nat) ( optional  (tuple ( uint64)( MultisigWallet_ι_UpdateRequestLRecord ) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00000L LocalFields00000I . 
Opaque LocalState00000LRecord . 
Inductive LocalFields00001I := | ι000010 | ι000011 .
Definition LocalState00001L := [( XHMap (string*nat) ( boolean)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00001L LocalFields00001I . 
Opaque LocalState00001LRecord . 
Inductive LocalFields00010I := | ι000100 | ι000101 .
Definition LocalState00010L := [( XHMap (string*nat) ( uint64)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00010L LocalFields00010I . 
Opaque LocalState00010LRecord . 
Inductive LocalFields00011I := | ι000110 | ι000111 .
Definition LocalState00011L := [( XHMap (string*nat) (MultisigWallet_ι_UpdateRequestLRecord)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00011L LocalFields00011I . 
Opaque LocalState00011LRecord . 
Inductive LocalFields00100I := | ι001000 | ι001001 .
Definition LocalState00100L := [( XHMap (string*nat) ( TvmCell)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00100L LocalFields00100I . 
Opaque LocalState00100LRecord . 
Inductive LocalFields00101I := | ι001010 | ι001011 .
Definition LocalState00101L := [( XHMap (string*nat) ( uint8)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00101L LocalFields00101I . 
Opaque LocalState00101LRecord . 
Inductive LocalFields00110I := | ι001100 | ι001101 .
Definition LocalState00110L := [( XHMap (string*nat) ( optional  (MultisigWallet_ι_UpdateRequestLRecord ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00110L LocalFields00110I . 
Opaque LocalState00110LRecord . 
Inductive LocalFields00111I := | ι001110 | ι001111 .
Definition LocalState00111L := [( XHMap (string*nat) ( uint32)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00111L LocalFields00111I . 
Opaque LocalState00111LRecord . 
Inductive LocalFields01000I := | ι010000 | ι010001 .
Definition LocalState01000L := [( XHMap (string*nat) (MultisigWallet_ι_Transaction[]LRecord)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01000L LocalFields01000I . 
Opaque LocalState01000LRecord . 
Inductive LocalFields01001I := | ι010010 | ι010011 .
Definition LocalState01001L := [( XHMap (string*nat) (MultisigWallet_ι_CustodianInfo[]LRecord)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01001L LocalFields01001I . 
Opaque LocalState01001LRecord . 
Inductive LocalFields01010I := | ι010100 | ι010101 .
Definition LocalState01010L := [( XHMap (string*nat) ( optional  ( uint256 ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01010L LocalFields01010I . 
Opaque LocalState01010LRecord . 
Inductive LocalFields01011I := | ι010110 | ι010111 .
Definition LocalState01011L := [( XHMap (string*nat) ( uint256)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01011L LocalFields01011I . 
Opaque LocalState01011LRecord . 
Inductive LocalFields01100I := | ι011000 | ι011001 .
Definition LocalState01100L := [( XHMap (string*nat) (MultisigWallet_ι_TransactionLRecord)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01100L LocalFields01100I . 
Opaque LocalState01100LRecord . 
Inductive LocalFields01101I := | ι011010 | ι011011 .
Definition LocalState01101L := [( XHMap (string*nat) ( optional  (MultisigWallet_ι_TransactionLRecord ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01101L LocalFields01101I . 
Opaque LocalState01101LRecord . 
Inductive LocalFields01110I := | ι011100 | ι011101 .
Definition LocalState01110L := [( XHMap (string*nat) ( optional  (tuple ( uint64)( MultisigWallet_ι_TransactionLRecord ) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01110L LocalFields01110I . 
Opaque LocalState01110LRecord . 
Inductive LocalFields01111I := | ι011110 | ι011111 .
Definition LocalState01111L := [( XHMap (string*nat) ( uint128)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01111L LocalFields01111I . 
Opaque LocalState01111LRecord . 
Inductive LocalFields10000I := | ι100000 | ι100001 .
Definition LocalState10000L := [( XHMap (string*nat) ( optional  ( uint8 ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10000L LocalFields10000I . 
Opaque LocalState10000LRecord . 
Inductive LocalFields10001I := | ι100010 | ι100011 .
Definition LocalState10001L := [( XHMap (string*nat) ( uint256[])) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10001L LocalFields10001I . 
Opaque LocalState10001LRecord . 
(**************** LocalState Tree ***************.
    /\
   /\\
  /\/\\
 /\/\/\/\\
/\/\/\/\/\/\/\/\/\
**************** LocalState Tree ***************)

Inductive LocalFields0000I := | ι00000 | ι00001 . 
Definition LocalState0000L := [ LocalState00000LRecord ; LocalState00001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0000L LocalFields0000I . 
Opaque LocalState0000LRecord . 

Inductive LocalFields0001I := | ι00010 | ι00011 . 
Definition LocalState0001L := [ LocalState00010LRecord ; LocalState00011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0001L LocalFields0001I . 
Opaque LocalState0001LRecord . 

Inductive LocalFields0010I := | ι00100 | ι00101 . 
Definition LocalState0010L := [ LocalState00100LRecord ; LocalState00101LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0010L LocalFields0010I . 
Opaque LocalState0010LRecord . 

Inductive LocalFields0011I := | ι00110 | ι00111 . 
Definition LocalState0011L := [ LocalState00110LRecord ; LocalState00111LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0011L LocalFields0011I . 
Opaque LocalState0011LRecord . 

Inductive LocalFields0100I := | ι01000 | ι01001 . 
Definition LocalState0100L := [ LocalState01000LRecord ; LocalState01001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0100L LocalFields0100I . 
Opaque LocalState0100LRecord . 

Inductive LocalFields0101I := | ι01010 | ι01011 . 
Definition LocalState0101L := [ LocalState01010LRecord ; LocalState01011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0101L LocalFields0101I . 
Opaque LocalState0101LRecord . 

Inductive LocalFields0110I := | ι01100 | ι01101 . 
Definition LocalState0110L := [ LocalState01100LRecord ; LocalState01101LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0110L LocalFields0110I . 
Opaque LocalState0110LRecord . 

Inductive LocalFields0111I := | ι01110 | ι01111 . 
Definition LocalState0111L := [ LocalState01110LRecord ; LocalState01111LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0111L LocalFields0111I . 
Opaque LocalState0111LRecord . 

Inductive LocalFields1000I := | ι10000 | ι10001 . 
Definition LocalState1000L := [ LocalState10000LRecord ; LocalState10001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState1000L LocalFields1000I . 
Opaque LocalState1000LRecord . 

Inductive LocalFields000I := | ι0000 | ι0001 . 
Definition LocalState000L := [ LocalState0000LRecord ; LocalState0001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState000L LocalFields000I . 
Opaque LocalState000LRecord . 

Inductive LocalFields001I := | ι0010 | ι0011 . 
Definition LocalState001L := [ LocalState0010LRecord ; LocalState0011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState001L LocalFields001I . 
Opaque LocalState001LRecord . 

Inductive LocalFields010I := | ι0100 | ι0101 . 
Definition LocalState010L := [ LocalState0100LRecord ; LocalState0101LRecord ] . 
GlobalGeneratePruvendoRecord LocalState010L LocalFields010I . 
Opaque LocalState010LRecord . 

Inductive LocalFields011I := | ι0110 | ι0111 . 
Definition LocalState011L := [ LocalState0110LRecord ; LocalState0111LRecord ] . 
GlobalGeneratePruvendoRecord LocalState011L LocalFields011I . 
Opaque LocalState011LRecord . 

Inductive LocalFields00I := | ι000 | ι001 . 
Definition LocalState00L := [ LocalState000LRecord ; LocalState001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState00L LocalFields00I . 
Opaque LocalState00LRecord . 

Inductive LocalFields01I := | ι010 | ι011 . 
Definition LocalState01L := [ LocalState010LRecord ; LocalState011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState01L LocalFields01I . 
Opaque LocalState01LRecord . 

Inductive LocalFields0I := | ι00 | ι01 . 
Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0L LocalFields0I . 
Opaque LocalState0LRecord . 

Inductive LocalFieldsI := | ι0 | ι1 . 
Definition LocalStateL := [ LocalState0LRecord ; LocalState1000LRecord ] . 
GlobalGeneratePruvendoRecord LocalStateL LocalFieldsI .
Opaque LocalStateLRecord . 


Transparent

LocalState00000LRecord
LocalState00001LRecord
LocalState00010LRecord
LocalState00011LRecord
LocalState00100LRecord
LocalState00101LRecord
LocalState00110LRecord
LocalState00111LRecord
LocalState01000LRecord
LocalState01001LRecord
LocalState01010LRecord
LocalState01011LRecord
LocalState01100LRecord
LocalState01101LRecord
LocalState01110LRecord
LocalState01111LRecord
LocalState10000LRecord
LocalState10001LRecord

LocalState0000LRecord
LocalState0001LRecord
LocalState0010LRecord
LocalState0011LRecord
LocalState0100LRecord
LocalState0101LRecord
LocalState0110LRecord
LocalState0111LRecord
LocalState1000LRecord

LocalState000LRecord
LocalState001LRecord
LocalState010LRecord
LocalState011LRecord

LocalState00LRecord
LocalState01LRecord

LocalState0LRecord.
Transparent LocalStateLRecord.
Notation LocalStateField := (LocalStateField XHMap LocalStateLRecord). 

#[global, program] Instance LocalStateField00000 : LocalStateField ( optional  (tuple ( uint64)( MultisigWallet_ι_UpdateRequestLRecord ) )).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00000).
eapply (LocalState00000LEmbeddedType ι000001). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00000).
eapply (LocalState00000LEmbeddedType ι000000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField00000 : typeclass_instances. 


#[global, program] Instance LocalStateField00001 : LocalStateField ( boolean).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00001).
eapply (LocalState00001LEmbeddedType ι000011). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00001).
eapply (LocalState00001LEmbeddedType ι000010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField00001 : typeclass_instances. 


#[global, program] Instance LocalStateField00010 : LocalStateField ( uint64).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00010).
eapply (LocalState00010LEmbeddedType ι000101). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00010).
eapply (LocalState00010LEmbeddedType ι000100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField00010 : typeclass_instances. 


#[global, program] Instance LocalStateField00011 : LocalStateField (MultisigWallet_ι_UpdateRequestLRecord).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00011).
eapply (LocalState00011LEmbeddedType ι000111). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00011).
eapply (LocalState00011LEmbeddedType ι000110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField00011 : typeclass_instances. 


#[global, program] Instance LocalStateField00100 : LocalStateField ( TvmCell).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00100).
eapply (LocalState00100LEmbeddedType ι001001). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00100).
eapply (LocalState00100LEmbeddedType ι001000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField00100 : typeclass_instances. 


#[global, program] Instance LocalStateField00101 : LocalStateField ( uint8).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00101).
eapply (LocalState00101LEmbeddedType ι001011). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00101).
eapply (LocalState00101LEmbeddedType ι001010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField00101 : typeclass_instances. 


#[global, program] Instance LocalStateField00110 : LocalStateField ( optional  (MultisigWallet_ι_UpdateRequestLRecord )).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00110).
eapply (LocalState00110LEmbeddedType ι001101). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00110).
eapply (LocalState00110LEmbeddedType ι001100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField00110 : typeclass_instances. 


#[global, program] Instance LocalStateField00111 : LocalStateField ( uint32).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00111).
eapply (LocalState00111LEmbeddedType ι001111). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00111).
eapply (LocalState00111LEmbeddedType ι001110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField00111 : typeclass_instances. 


#[global, program] Instance LocalStateField01000 : LocalStateField (MultisigWallet_ι_Transaction[]LRecord).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01000).
eapply (LocalState01000LEmbeddedType ι010001). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01000).
eapply (LocalState01000LEmbeddedType ι010000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField01000 : typeclass_instances. 


#[global, program] Instance LocalStateField01001 : LocalStateField (MultisigWallet_ι_CustodianInfo[]LRecord).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01001).
eapply (LocalState01001LEmbeddedType ι010011). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01001).
eapply (LocalState01001LEmbeddedType ι010010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField01001 : typeclass_instances. 


#[global, program] Instance LocalStateField01010 : LocalStateField ( optional  ( uint256 )).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01010).
eapply (LocalState01010LEmbeddedType ι010101). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01010).
eapply (LocalState01010LEmbeddedType ι010100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField01010 : typeclass_instances. 


#[global, program] Instance LocalStateField01011 : LocalStateField ( uint256).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01011).
eapply (LocalState01011LEmbeddedType ι010111). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01011).
eapply (LocalState01011LEmbeddedType ι010110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField01011 : typeclass_instances. 


#[global, program] Instance LocalStateField01100 : LocalStateField (MultisigWallet_ι_TransactionLRecord).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01100).
eapply (LocalState01100LEmbeddedType ι011001). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01100).
eapply (LocalState01100LEmbeddedType ι011000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField01100 : typeclass_instances. 


#[global, program] Instance LocalStateField01101 : LocalStateField ( optional  (MultisigWallet_ι_TransactionLRecord )).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01101).
eapply (LocalState01101LEmbeddedType ι011011). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01101).
eapply (LocalState01101LEmbeddedType ι011010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField01101 : typeclass_instances. 


#[global, program] Instance LocalStateField01110 : LocalStateField ( optional  (tuple ( uint64)( MultisigWallet_ι_TransactionLRecord ) )).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01110).
eapply (LocalState01110LEmbeddedType ι011101). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01110).
eapply (LocalState01110LEmbeddedType ι011100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField01110 : typeclass_instances. 


#[global, program] Instance LocalStateField01111 : LocalStateField ( uint128).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01111).
eapply (LocalState01111LEmbeddedType ι011111). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01111).
eapply (LocalState01111LEmbeddedType ι011110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField01111 : typeclass_instances. 


#[global, program] Instance LocalStateField10000 : LocalStateField ( optional  ( uint8 )).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10000).
eapply (LocalState10000LEmbeddedType ι100001). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10000).
eapply (LocalState10000LEmbeddedType ι100000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField10000 : typeclass_instances. 


#[global, program] Instance LocalStateField10001 : LocalStateField ( uint256[]).
Next Obligation. 

eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10001).
eapply (LocalState10001LEmbeddedType ι100011). 
Defined.
Next Obligation. 

eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10001).
eapply (LocalState10001LEmbeddedType ι100010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField10001 : typeclass_instances. 
