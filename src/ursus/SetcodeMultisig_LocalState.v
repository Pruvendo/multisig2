(*/Users/petrlarockin/Downloads/TON/solidity-coq-translator/ref*)
Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import SetcodeMultisig.

Inductive LocalFields000000I := | ι0000000 | ι0000001 .
Definition LocalState000000L := [( XHMap (string*nat) ( uint64)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState000000L LocalFields000000I . 
Opaque LocalState000000LRecord . 
Inductive LocalFields000001I := | ι0000010 | ι0000011 .
Definition LocalState000001L := [( XHMap (string*nat) ( uint8)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState000001L LocalFields000001I . 
Opaque LocalState000001LRecord . 
Inductive LocalFields000010I := | ι0000100 | ι0000101 .
Definition LocalState000010L := [( XHMap (string*nat) ( optional  (tuple ( uint64)( (UpdateRequestLRecord) ) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState000010L LocalFields000010I . 
Opaque LocalState000010LRecord . 
Inductive LocalFields000011I := | ι0000110 | ι0000111 .
Definition LocalState000011L := [( XHMap (string*nat) ( boolean)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState000011L LocalFields000011I . 
Opaque LocalState000011LRecord . 
Inductive LocalFields000100I := | ι0001000 | ι0001001 .
Definition LocalState000100L := [( XHMap (string*nat) ((UpdateRequestLRecord))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState000100L LocalFields000100I . 
Opaque LocalState000100LRecord . 
Inductive LocalFields000101I := | ι0001010 | ι0001011 .
Definition LocalState000101L := [( XHMap (string*nat) ( uint32)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState000101L LocalFields000101I . 
Opaque LocalState000101LRecord . 
Inductive LocalFields000110I := | ι0001100 | ι0001101 .
Definition LocalState000110L := [( XHMap (string*nat) ( TvmSlice)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState000110L LocalFields000110I . 
Opaque LocalState000110LRecord . 
Inductive LocalFields000111I := | ι0001110 | ι0001111 .
Definition LocalState000111L := [( XHMap (string*nat) ( optional  ( uint256[] ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState000111L LocalFields000111I . 
Opaque LocalState000111LRecord . 
Inductive LocalFields001000I := | ι0010000 | ι0010001 .
Definition LocalState001000L := [( XHMap (string*nat) ( TvmCell)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState001000L LocalFields001000I . 
Opaque LocalState001000LRecord . 
Inductive LocalFields001001I := | ι0010010 | ι0010011 .
Definition LocalState001001L := [( XHMap (string*nat) ( uint256[])) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState001001L LocalFields001001I . 
Opaque LocalState001001LRecord . 
Inductive LocalFields001010I := | ι0010100 | ι0010101 .
Definition LocalState001010L := [( XHMap (string*nat) ((UpdateRequestLRecord[]))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState001010L LocalFields001010I . 
Opaque LocalState001010LRecord . 
Inductive LocalFields001011I := | ι0010110 | ι0010111 .
Definition LocalState001011L := [( XHMap (string*nat) ( builder_)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState001011L LocalFields001011I . 
Opaque LocalState001011LRecord . 
Inductive LocalFields001100I := | ι0011000 | ι0011001 .
Definition LocalState001100L := [( XHMap (string*nat) ( optional  ((UpdateRequestLRecord) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState001100L LocalFields001100I . 
Opaque LocalState001100LRecord . 
Inductive LocalFields001101I := | ι0011010 | ι0011011 .
Definition LocalState001101L := [( XHMap (string*nat) ( optional  ( TvmCell ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState001101L LocalFields001101I . 
Opaque LocalState001101LRecord . 
Inductive LocalFields001110I := | ι0011100 | ι0011101 .
Definition LocalState001110L := [( XHMap (string*nat) ( uint256)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState001110L LocalFields001110I . 
Opaque LocalState001110LRecord . 
Inductive LocalFields001111I := | ι0011110 | ι0011111 .
Definition LocalState001111L := [( XHMap (string*nat) ( optional  ( uint256 ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState001111L LocalFields001111I . 
Opaque LocalState001111LRecord . 
Inductive LocalFields010000I := | ι0100000 | ι0100001 .
Definition LocalState010000L := [( XHMap (string*nat) ( optional  ( uint8 ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState010000L LocalFields010000I . 
Opaque LocalState010000LRecord . 
Inductive LocalFields010001I := | ι0100010 | ι0100011 .
Definition LocalState010001L := [( XHMap (string*nat) ( optional  ( uint32 ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState010001L LocalFields010001I . 
Opaque LocalState010001LRecord . 
Inductive LocalFields010010I := | ι0100100 | ι0100101 .
Definition LocalState010010L := [( XHMap (string*nat) ((CustodianInfoLRecord[]))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState010010L LocalFields010010I . 
Opaque LocalState010010LRecord . 
Inductive LocalFields010011I := | ι0100110 | ι0100111 .
Definition LocalState010011L := [( XHMap (string*nat) ((TransactionLRecord))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState010011L LocalFields010011I . 
Opaque LocalState010011LRecord . 
Inductive LocalFields010100I := | ι0101000 | ι0101001 .
Definition LocalState010100L := [( XHMap (string*nat) ((TransactionLRecord[]))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState010100L LocalFields010100I . 
Opaque LocalState010100LRecord . 
Inductive LocalFields010101I := | ι0101010 | ι0101011 .
Definition LocalState010101L := [( XHMap (string*nat) ( optional  ((TransactionLRecord) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState010101L LocalFields010101I . 
Opaque LocalState010101LRecord . 
Inductive LocalFields010110I := | ι0101100 | ι0101101 .
Definition LocalState010110L := [( XHMap (string*nat) ( uint128)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState010110L LocalFields010110I . 
Opaque LocalState010110LRecord . 
Inductive LocalFields010111I := | ι0101110 | ι0101111 .
Definition LocalState010111L := [( XHMap (string*nat) ( optional  (tuple ( uint64)( (TransactionLRecord) ) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState010111L LocalFields010111I . 
Opaque LocalState010111LRecord . 
Inductive LocalFields011000I := | ι0110000 | ι0110001 .
Definition LocalState011000L := [( XHMap (string*nat) ( address)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState011000L LocalFields011000I . 
Opaque LocalState011000LRecord . 
Inductive LocalFields011001I := | ι0110010 | ι0110011 .
Definition LocalState011001L := [( XHMap (string*nat) ( optional (tuple(bool) (TvmSlice)))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState011001L LocalFields011001I . 
Opaque LocalState011001LRecord . 
Inductive LocalFields011010I := | ι0110100 | ι0110101 .
Definition LocalState011010L := [( XHMap (string*nat) ( optional (tuple(uint256[]) (TvmSlice)))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState011010L LocalFields011010I . 
Opaque LocalState011010LRecord . 
Inductive LocalFields011011I := | ι0110110 | ι0110111 .
Definition LocalState011011L := [( XHMap (string*nat) ( optional ((mapping uint256 uint8 ** (uint8 * uint256)) ** TvmSlice))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState011011L LocalFields011011I . 
Opaque LocalState011011LRecord . 
Inductive LocalFields011100I := | ι0111000 | ι0111001 .
Definition LocalState011100L := [( XHMap (string*nat) ( (mapping uint256 uint8 ** (uint8 ** uint256)))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState011100L LocalFields011100I . 
Opaque LocalState011100LRecord . 
Inductive LocalFields011101I := | ι0111010 | ι0111011 .
Definition LocalState011101L := [( XHMap (string*nat) ( optional ((uint8 ** uint32) ** TvmSlice))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState011101L LocalFields011101I . 
Opaque LocalState011101LRecord . 
Inductive LocalFields011110I := | ι0111100 | ι0111101 .
Definition LocalState011110L := [( XHMap (string*nat) ( (uint8 ** uint32))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState011110L LocalFields011110I . 
Opaque LocalState011110LRecord . 
Inductive LocalFields011111I := | ι0111110 | ι0111111 .
Definition LocalState011111L := [( XHMap (string*nat) ( (optional TvmBuilder))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState011111L LocalFields011111I . 
Opaque LocalState011111LRecord . 
Inductive LocalFields100000I := | ι1000000 | ι1000001 .
Definition LocalState100000L := [( XHMap (string*nat) ( ( uint8**uint128 ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState100000L LocalFields100000I . 
Opaque LocalState100000LRecord . 
(**************** LocalState Tree ***************.
     /\
    /\\
   /\/\\
  /\/\/\/\\
 /\/\/\/\/\/\/\/\\
/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\\
**************** LocalState Tree ***************)

Inductive LocalFields00000I := | ι000000 | ι000001 . 
Definition LocalState00000L := [ LocalState000000LRecord ; LocalState000001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState00000L LocalFields00000I . 
Opaque LocalState00000LRecord . 

Inductive LocalFields00001I := | ι000010 | ι000011 . 
Definition LocalState00001L := [ LocalState000010LRecord ; LocalState000011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState00001L LocalFields00001I . 
Opaque LocalState00001LRecord . 

Inductive LocalFields00010I := | ι000100 | ι000101 . 
Definition LocalState00010L := [ LocalState000100LRecord ; LocalState000101LRecord ] . 
GlobalGeneratePruvendoRecord LocalState00010L LocalFields00010I . 
Opaque LocalState00010LRecord . 

Inductive LocalFields00011I := | ι000110 | ι000111 . 
Definition LocalState00011L := [ LocalState000110LRecord ; LocalState000111LRecord ] . 
GlobalGeneratePruvendoRecord LocalState00011L LocalFields00011I . 
Opaque LocalState00011LRecord . 

Inductive LocalFields00100I := | ι001000 | ι001001 . 
Definition LocalState00100L := [ LocalState001000LRecord ; LocalState001001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState00100L LocalFields00100I . 
Opaque LocalState00100LRecord . 

Inductive LocalFields00101I := | ι001010 | ι001011 . 
Definition LocalState00101L := [ LocalState001010LRecord ; LocalState001011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState00101L LocalFields00101I . 
Opaque LocalState00101LRecord . 

Inductive LocalFields00110I := | ι001100 | ι001101 . 
Definition LocalState00110L := [ LocalState001100LRecord ; LocalState001101LRecord ] . 
GlobalGeneratePruvendoRecord LocalState00110L LocalFields00110I . 
Opaque LocalState00110LRecord . 

Inductive LocalFields00111I := | ι001110 | ι001111 . 
Definition LocalState00111L := [ LocalState001110LRecord ; LocalState001111LRecord ] . 
GlobalGeneratePruvendoRecord LocalState00111L LocalFields00111I . 
Opaque LocalState00111LRecord . 

Inductive LocalFields01000I := | ι010000 | ι010001 . 
Definition LocalState01000L := [ LocalState010000LRecord ; LocalState010001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState01000L LocalFields01000I . 
Opaque LocalState01000LRecord . 

Inductive LocalFields01001I := | ι010010 | ι010011 . 
Definition LocalState01001L := [ LocalState010010LRecord ; LocalState010011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState01001L LocalFields01001I . 
Opaque LocalState01001LRecord . 

Inductive LocalFields01010I := | ι010100 | ι010101 . 
Definition LocalState01010L := [ LocalState010100LRecord ; LocalState010101LRecord ] . 
GlobalGeneratePruvendoRecord LocalState01010L LocalFields01010I . 
Opaque LocalState01010LRecord . 

Inductive LocalFields01011I := | ι010110 | ι010111 . 
Definition LocalState01011L := [ LocalState010110LRecord ; LocalState010111LRecord ] . 
GlobalGeneratePruvendoRecord LocalState01011L LocalFields01011I . 
Opaque LocalState01011LRecord . 

Inductive LocalFields01100I := | ι011000 | ι011001 . 
Definition LocalState01100L := [ LocalState011000LRecord ; LocalState011001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState01100L LocalFields01100I . 
Opaque LocalState01100LRecord . 

Inductive LocalFields01101I := | ι011010 | ι011011 . 
Definition LocalState01101L := [ LocalState011010LRecord ; LocalState011011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState01101L LocalFields01101I . 
Opaque LocalState01101LRecord . 

Inductive LocalFields01110I := | ι011100 | ι011101 . 
Definition LocalState01110L := [ LocalState011100LRecord ; LocalState011101LRecord ] . 
GlobalGeneratePruvendoRecord LocalState01110L LocalFields01110I . 
Opaque LocalState01110LRecord . 

Inductive LocalFields01111I := | ι011110 | ι011111 . 
Definition LocalState01111L := [ LocalState011110LRecord ; LocalState011111LRecord ] . 
GlobalGeneratePruvendoRecord LocalState01111L LocalFields01111I . 
Opaque LocalState01111LRecord . 

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
Definition LocalStateL := [ LocalState0LRecord ; LocalState100000LRecord ] . 
GlobalGeneratePruvendoRecord LocalStateL LocalFieldsI .
Opaque LocalStateLRecord . 
Transparent

LocalState000000LRecord
LocalState000001LRecord
LocalState000010LRecord
LocalState000011LRecord
LocalState000100LRecord
LocalState000101LRecord
LocalState000110LRecord
LocalState000111LRecord
LocalState001000LRecord
LocalState001001LRecord
LocalState001010LRecord
LocalState001011LRecord
LocalState001100LRecord
LocalState001101LRecord
LocalState001110LRecord
LocalState001111LRecord
LocalState010000LRecord
LocalState010001LRecord
LocalState010010LRecord
LocalState010011LRecord
LocalState010100LRecord
LocalState010101LRecord
LocalState010110LRecord
LocalState010111LRecord
LocalState011000LRecord
LocalState011001LRecord
LocalState011010LRecord
LocalState011011LRecord
LocalState011100LRecord
LocalState011101LRecord
LocalState011110LRecord
LocalState011111LRecord
LocalState100000LRecord

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

LocalState0000LRecord
LocalState0001LRecord
LocalState0010LRecord
LocalState0011LRecord
LocalState0100LRecord
LocalState0101LRecord
LocalState0110LRecord
LocalState0111LRecord

LocalState000LRecord
LocalState001LRecord
LocalState010LRecord
LocalState011LRecord

LocalState00LRecord
LocalState01LRecord

LocalState0LRecord.
Transparent LocalStateLRecord.
Notation LocalStateField := (LocalStateField XHMap LocalStateLRecord).
#[global, program] Instance LocalStateField000000 : LocalStateField ( uint64).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00000). 
eapply TransEmbedded. eapply (_ ι000000).
eapply (LocalState000000LEmbeddedType ι0000001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00000). 
eapply TransEmbedded. eapply (_ ι000000).
eapply (LocalState000000LEmbeddedType ι0000000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField000000 : typeclass_instances. 

#[global, program] Instance LocalStateField000001 : LocalStateField ( uint8).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00000). 
eapply TransEmbedded. eapply (_ ι000001).
eapply (LocalState000001LEmbeddedType ι0000011). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00000). 
eapply TransEmbedded. eapply (_ ι000001).
eapply (LocalState000001LEmbeddedType ι0000010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField000001 : typeclass_instances. 

#[global, program] Instance LocalStateField000010 : LocalStateField ( optional  (tuple ( uint64)( (UpdateRequestLRecord) ) )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00001). 
eapply TransEmbedded. eapply (_ ι000010).
eapply (LocalState000010LEmbeddedType ι0000101). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00001). 
eapply TransEmbedded. eapply (_ ι000010).
eapply (LocalState000010LEmbeddedType ι0000100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField000010 : typeclass_instances. 

#[global, program] Instance LocalStateField000011 : LocalStateField ( boolean).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00001). 
eapply TransEmbedded. eapply (_ ι000011).
eapply (LocalState000011LEmbeddedType ι0000111). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000). 
eapply TransEmbedded. eapply (_ ι00001). 
eapply TransEmbedded. eapply (_ ι000011).
eapply (LocalState000011LEmbeddedType ι0000110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField000011 : typeclass_instances. 

#[global, program] Instance LocalStateField000100 : LocalStateField ((UpdateRequestLRecord)).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00010). 
eapply TransEmbedded. eapply (_ ι000100).
eapply (LocalState000100LEmbeddedType ι0001001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00010). 
eapply TransEmbedded. eapply (_ ι000100).
eapply (LocalState000100LEmbeddedType ι0001000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField000100 : typeclass_instances. 

#[global, program] Instance LocalStateField000101 : LocalStateField ( uint32).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00010). 
eapply TransEmbedded. eapply (_ ι000101).
eapply (LocalState000101LEmbeddedType ι0001011). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00010). 
eapply TransEmbedded. eapply (_ ι000101).
eapply (LocalState000101LEmbeddedType ι0001010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField000101 : typeclass_instances. 

#[global, program] Instance LocalStateField000110 : LocalStateField ( TvmSlice).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00011). 
eapply TransEmbedded. eapply (_ ι000110).
eapply (LocalState000110LEmbeddedType ι0001101). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00011). 
eapply TransEmbedded. eapply (_ ι000110).
eapply (LocalState000110LEmbeddedType ι0001100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField000110 : typeclass_instances. 

#[global, program] Instance LocalStateField000111 : LocalStateField ( optional  ( uint256[] )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00011). 
eapply TransEmbedded. eapply (_ ι000111).
eapply (LocalState000111LEmbeddedType ι0001111). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001). 
eapply TransEmbedded. eapply (_ ι00011). 
eapply TransEmbedded. eapply (_ ι000111).
eapply (LocalState000111LEmbeddedType ι0001110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField000111 : typeclass_instances. 

#[global, program] Instance LocalStateField001000 : LocalStateField ( TvmCell).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00100). 
eapply TransEmbedded. eapply (_ ι001000).
eapply (LocalState001000LEmbeddedType ι0010001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00100). 
eapply TransEmbedded. eapply (_ ι001000).
eapply (LocalState001000LEmbeddedType ι0010000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField001000 : typeclass_instances. 

#[global, program] Instance LocalStateField001001 : LocalStateField ( uint256[]).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00100). 
eapply TransEmbedded. eapply (_ ι001001).
eapply (LocalState001001LEmbeddedType ι0010011). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00100). 
eapply TransEmbedded. eapply (_ ι001001).
eapply (LocalState001001LEmbeddedType ι0010010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField001001 : typeclass_instances. 

#[global, program] Instance LocalStateField001010 : LocalStateField ((UpdateRequestLRecord[])).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00101). 
eapply TransEmbedded. eapply (_ ι001010).
eapply (LocalState001010LEmbeddedType ι0010101). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00101). 
eapply TransEmbedded. eapply (_ ι001010).
eapply (LocalState001010LEmbeddedType ι0010100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField001010 : typeclass_instances. 

#[global, program] Instance LocalStateField001011 : LocalStateField ( builder_).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00101). 
eapply TransEmbedded. eapply (_ ι001011).
eapply (LocalState001011LEmbeddedType ι0010111). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010). 
eapply TransEmbedded. eapply (_ ι00101). 
eapply TransEmbedded. eapply (_ ι001011).
eapply (LocalState001011LEmbeddedType ι0010110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField001011 : typeclass_instances. 

#[global, program] Instance LocalStateField001100 : LocalStateField ( optional  ((UpdateRequestLRecord) )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00110). 
eapply TransEmbedded. eapply (_ ι001100).
eapply (LocalState001100LEmbeddedType ι0011001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00110). 
eapply TransEmbedded. eapply (_ ι001100).
eapply (LocalState001100LEmbeddedType ι0011000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField001100 : typeclass_instances. 

#[global, program] Instance LocalStateField001101 : LocalStateField ( optional  ( TvmCell )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00110). 
eapply TransEmbedded. eapply (_ ι001101).
eapply (LocalState001101LEmbeddedType ι0011011). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00110). 
eapply TransEmbedded. eapply (_ ι001101).
eapply (LocalState001101LEmbeddedType ι0011010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField001101 : typeclass_instances. 

#[global, program] Instance LocalStateField001110 : LocalStateField ( uint256).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00111). 
eapply TransEmbedded. eapply (_ ι001110).
eapply (LocalState001110LEmbeddedType ι0011101). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00111). 
eapply TransEmbedded. eapply (_ ι001110).
eapply (LocalState001110LEmbeddedType ι0011100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField001110 : typeclass_instances. 

#[global, program] Instance LocalStateField001111 : LocalStateField ( optional  ( uint256 )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00111). 
eapply TransEmbedded. eapply (_ ι001111).
eapply (LocalState001111LEmbeddedType ι0011111). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011). 
eapply TransEmbedded. eapply (_ ι00111). 
eapply TransEmbedded. eapply (_ ι001111).
eapply (LocalState001111LEmbeddedType ι0011110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField001111 : typeclass_instances. 

#[global, program] Instance LocalStateField010000 : LocalStateField ( optional  ( uint8 )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01000). 
eapply TransEmbedded. eapply (_ ι010000).
eapply (LocalState010000LEmbeddedType ι0100001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01000). 
eapply TransEmbedded. eapply (_ ι010000).
eapply (LocalState010000LEmbeddedType ι0100000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField010000 : typeclass_instances. 

#[global, program] Instance LocalStateField010001 : LocalStateField ( optional  ( uint32 )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01000). 
eapply TransEmbedded. eapply (_ ι010001).
eapply (LocalState010001LEmbeddedType ι0100011). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01000). 
eapply TransEmbedded. eapply (_ ι010001).
eapply (LocalState010001LEmbeddedType ι0100010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField010001 : typeclass_instances. 

#[global, program] Instance LocalStateField010010 : LocalStateField ((CustodianInfoLRecord[])).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01001). 
eapply TransEmbedded. eapply (_ ι010010).
eapply (LocalState010010LEmbeddedType ι0100101). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01001). 
eapply TransEmbedded. eapply (_ ι010010).
eapply (LocalState010010LEmbeddedType ι0100100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField010010 : typeclass_instances. 

#[global, program] Instance LocalStateField010011 : LocalStateField ((TransactionLRecord)).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01001). 
eapply TransEmbedded. eapply (_ ι010011).
eapply (LocalState010011LEmbeddedType ι0100111). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100). 
eapply TransEmbedded. eapply (_ ι01001). 
eapply TransEmbedded. eapply (_ ι010011).
eapply (LocalState010011LEmbeddedType ι0100110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField010011 : typeclass_instances. 

#[global, program] Instance LocalStateField010100 : LocalStateField ((TransactionLRecord[])).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01010). 
eapply TransEmbedded. eapply (_ ι010100).
eapply (LocalState010100LEmbeddedType ι0101001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01010). 
eapply TransEmbedded. eapply (_ ι010100).
eapply (LocalState010100LEmbeddedType ι0101000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField010100 : typeclass_instances. 

#[global, program] Instance LocalStateField010101 : LocalStateField ( optional  ((TransactionLRecord) )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01010). 
eapply TransEmbedded. eapply (_ ι010101).
eapply (LocalState010101LEmbeddedType ι0101011). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01010). 
eapply TransEmbedded. eapply (_ ι010101).
eapply (LocalState010101LEmbeddedType ι0101010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField010101 : typeclass_instances. 

#[global, program] Instance LocalStateField010110 : LocalStateField ( uint128).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01011). 
eapply TransEmbedded. eapply (_ ι010110).
eapply (LocalState010110LEmbeddedType ι0101101). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01011). 
eapply TransEmbedded. eapply (_ ι010110).
eapply (LocalState010110LEmbeddedType ι0101100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField010110 : typeclass_instances. 

#[global, program] Instance LocalStateField010111 : LocalStateField ( optional  (tuple ( uint64)( (TransactionLRecord) ) )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01011). 
eapply TransEmbedded. eapply (_ ι010111).
eapply (LocalState010111LEmbeddedType ι0101111). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101). 
eapply TransEmbedded. eapply (_ ι01011). 
eapply TransEmbedded. eapply (_ ι010111).
eapply (LocalState010111LEmbeddedType ι0101110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField010111 : typeclass_instances. 

#[global, program] Instance LocalStateField011000 : LocalStateField ( address).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01100). 
eapply TransEmbedded. eapply (_ ι011000).
eapply (LocalState011000LEmbeddedType ι0110001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01100). 
eapply TransEmbedded. eapply (_ ι011000).
eapply (LocalState011000LEmbeddedType ι0110000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField011000 : typeclass_instances. 

#[global, program] Instance LocalStateField011001 : LocalStateField ( optional (tuple(bool) (TvmSlice))).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01100). 
eapply TransEmbedded. eapply (_ ι011001).
eapply (LocalState011001LEmbeddedType ι0110011). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01100). 
eapply TransEmbedded. eapply (_ ι011001).
eapply (LocalState011001LEmbeddedType ι0110010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField011001 : typeclass_instances. 

#[global, program] Instance LocalStateField011010 : LocalStateField ( optional (tuple(uint256[]) (TvmSlice))).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01101). 
eapply TransEmbedded. eapply (_ ι011010).
eapply (LocalState011010LEmbeddedType ι0110101). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01101). 
eapply TransEmbedded. eapply (_ ι011010).
eapply (LocalState011010LEmbeddedType ι0110100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField011010 : typeclass_instances. 

#[global, program] Instance LocalStateField011011 : LocalStateField ( optional ((mapping uint256 uint8 ** (uint8 * uint256)) ** TvmSlice)).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01101). 
eapply TransEmbedded. eapply (_ ι011011).
eapply (LocalState011011LEmbeddedType ι0110111). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110). 
eapply TransEmbedded. eapply (_ ι01101). 
eapply TransEmbedded. eapply (_ ι011011).
eapply (LocalState011011LEmbeddedType ι0110110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField011011 : typeclass_instances. 

#[global, program] Instance LocalStateField011100 : LocalStateField ( (mapping uint256 uint8 ** (uint8 ** uint256))).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01110). 
eapply TransEmbedded. eapply (_ ι011100).
eapply (LocalState011100LEmbeddedType ι0111001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01110). 
eapply TransEmbedded. eapply (_ ι011100).
eapply (LocalState011100LEmbeddedType ι0111000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField011100 : typeclass_instances. 

#[global, program] Instance LocalStateField011101 : LocalStateField ( optional ((uint8 ** uint32) ** TvmSlice)).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01110). 
eapply TransEmbedded. eapply (_ ι011101).
eapply (LocalState011101LEmbeddedType ι0111011). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01110). 
eapply TransEmbedded. eapply (_ ι011101).
eapply (LocalState011101LEmbeddedType ι0111010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField011101 : typeclass_instances. 

#[global, program] Instance LocalStateField011110 : LocalStateField ( (uint8 ** uint32)).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01111). 
eapply TransEmbedded. eapply (_ ι011110).
eapply (LocalState011110LEmbeddedType ι0111101). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01111). 
eapply TransEmbedded. eapply (_ ι011110).
eapply (LocalState011110LEmbeddedType ι0111100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField011110 : typeclass_instances. 

#[global, program] Instance LocalStateField011111 : LocalStateField ( (optional TvmBuilder)).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01111). 
eapply TransEmbedded. eapply (_ ι011111).
eapply (LocalState011111LEmbeddedType ι0111111). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111). 
eapply TransEmbedded. eapply (_ ι01111). 
eapply TransEmbedded. eapply (_ ι011111).
eapply (LocalState011111LEmbeddedType ι0111110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField011111 : typeclass_instances. 

#[global, program] Instance LocalStateField100000 : LocalStateField ( ( uint8**uint128 )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 

eapply (LocalState100000LEmbeddedType ι1000001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 

eapply (LocalState100000LEmbeddedType ι1000000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField100000 : typeclass_instances. 