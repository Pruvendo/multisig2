(*/Users/petrlarockin/Downloads/TON/solidity-coq-translator/ref*)
Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import SetcodeMultisig.
Inductive LocalFields00000I := | ι000000 | ι000001 .
Definition LocalState00000L := [( XHMap (string*nat) ( uint64)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00000L LocalFields00000I . 
Opaque LocalState00000LRecord . 
Inductive LocalFields00001I := | ι000010 | ι000011 .
Definition LocalState00001L := [( XHMap (string*nat) ( uint8)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00001L LocalFields00001I . 
Opaque LocalState00001LRecord . 
Inductive LocalFields00010I := | ι000100 | ι000101 .
Definition LocalState00010L := [( XHMap (string*nat) ( optional  (tuple ( uint64)( (UpdateRequestLRecord) ) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00010L LocalFields00010I . 
Opaque LocalState00010LRecord . 
Inductive LocalFields00011I := | ι000110 | ι000111 .
Definition LocalState00011L := [( XHMap (string*nat) ( boolean)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00011L LocalFields00011I . 
Opaque LocalState00011LRecord . 
Inductive LocalFields00100I := | ι001000 | ι001001 .
Definition LocalState00100L := [( XHMap (string*nat) ((UpdateRequestLRecord))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00100L LocalFields00100I . 
Opaque LocalState00100LRecord . 
Inductive LocalFields00101I := | ι001010 | ι001011 .
Definition LocalState00101L := [( XHMap (string*nat) ( uint32)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00101L LocalFields00101I . 
Opaque LocalState00101LRecord . 
Inductive LocalFields00110I := | ι001100 | ι001101 .
Definition LocalState00110L := [( XHMap (string*nat) ( slice_)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00110L LocalFields00110I . 
Opaque LocalState00110LRecord . 
Inductive LocalFields00111I := | ι001110 | ι001111 .
Definition LocalState00111L := [( XHMap (string*nat) ( optional  ( uint256[] ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00111L LocalFields00111I . 
Opaque LocalState00111LRecord . 
Inductive LocalFields01000I := | ι010000 | ι010001 .
Definition LocalState01000L := [( XHMap (string*nat) ( TvmCell)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01000L LocalFields01000I . 
Opaque LocalState01000LRecord . 
Inductive LocalFields01001I := | ι010010 | ι010011 .
Definition LocalState01001L := [( XHMap (string*nat) ( uint256[])) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01001L LocalFields01001I . 
Opaque LocalState01001LRecord . 
Inductive LocalFields01010I := | ι010100 | ι010101 .
Definition LocalState01010L := [( XHMap (string*nat) ((UpdateRequestLRecord[]))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01010L LocalFields01010I . 
Opaque LocalState01010LRecord . 
Inductive LocalFields01011I := | ι010110 | ι010111 .
Definition LocalState01011L := [( XHMap (string*nat) ( builder_)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01011L LocalFields01011I . 
Opaque LocalState01011LRecord . 
Inductive LocalFields01100I := | ι011000 | ι011001 .
Definition LocalState01100L := [( XHMap (string*nat) ( optional  ((UpdateRequestLRecord) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01100L LocalFields01100I . 
Opaque LocalState01100LRecord . 
Inductive LocalFields01101I := | ι011010 | ι011011 .
Definition LocalState01101L := [( XHMap (string*nat) ( optional  ( TvmCell ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01101L LocalFields01101I . 
Opaque LocalState01101LRecord . 
Inductive LocalFields01110I := | ι011100 | ι011101 .
Definition LocalState01110L := [( XHMap (string*nat) ( uint256)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01110L LocalFields01110I . 
Opaque LocalState01110LRecord . 
Inductive LocalFields01111I := | ι011110 | ι011111 .
Definition LocalState01111L := [( XHMap (string*nat) ( optional  ( uint256 ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01111L LocalFields01111I . 
Opaque LocalState01111LRecord . 
Inductive LocalFields10000I := | ι100000 | ι100001 .
Definition LocalState10000L := [( XHMap (string*nat) ( optional  ( uint8 ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10000L LocalFields10000I . 
Opaque LocalState10000LRecord . 
Inductive LocalFields10001I := | ι100010 | ι100011 .
Definition LocalState10001L := [( XHMap (string*nat) ( optional  ( uint32 ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10001L LocalFields10001I . 
Opaque LocalState10001LRecord . 
Inductive LocalFields10010I := | ι100100 | ι100101 .
Definition LocalState10010L := [( XHMap (string*nat) ((CustodianInfoLRecord[]))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10010L LocalFields10010I . 
Opaque LocalState10010LRecord . 
Inductive LocalFields10011I := | ι100110 | ι100111 .
Definition LocalState10011L := [( XHMap (string*nat) ((TransactionLRecord))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10011L LocalFields10011I . 
Opaque LocalState10011LRecord . 
Inductive LocalFields10100I := | ι101000 | ι101001 .
Definition LocalState10100L := [( XHMap (string*nat) ((TransactionLRecord[]))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10100L LocalFields10100I . 
Opaque LocalState10100LRecord . 
Inductive LocalFields10101I := | ι101010 | ι101011 .
Definition LocalState10101L := [( XHMap (string*nat) ( optional  ((TransactionLRecord) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10101L LocalFields10101I . 
Opaque LocalState10101LRecord . 
Inductive LocalFields10110I := | ι101100 | ι101101 .
Definition LocalState10110L := [( XHMap (string*nat) ( uint128)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10110L LocalFields10110I . 
Opaque LocalState10110LRecord . 
Inductive LocalFields10111I := | ι101110 | ι101111 .
Definition LocalState10111L := [( XHMap (string*nat) ( optional  (tuple ( uint64)( (TransactionLRecord) ) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10111L LocalFields10111I . 
Opaque LocalState10111LRecord . 
Inductive LocalFields11000I := | ι110000 | ι110001 .
Definition LocalState11000L := [( XHMap (string*nat) ( address)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState11000L LocalFields11000I . 
Opaque LocalState11000LRecord . 
(**************** LocalState Tree ***************.
    /\
   /\/\
  /\/\/\\
 /\/\/\/\/\/\\
/\/\/\/\/\/\/\/\/\/\/\/\\
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

Inductive LocalFields1001I := | ι10010 | ι10011 . 
Definition LocalState1001L := [ LocalState10010LRecord ; LocalState10011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState1001L LocalFields1001I . 
Opaque LocalState1001LRecord . 

Inductive LocalFields1010I := | ι10100 | ι10101 . 
Definition LocalState1010L := [ LocalState10100LRecord ; LocalState10101LRecord ] . 
GlobalGeneratePruvendoRecord LocalState1010L LocalFields1010I . 
Opaque LocalState1010LRecord . 

Inductive LocalFields1011I := | ι10110 | ι10111 . 
Definition LocalState1011L := [ LocalState10110LRecord ; LocalState10111LRecord ] . 
GlobalGeneratePruvendoRecord LocalState1011L LocalFields1011I . 
Opaque LocalState1011LRecord . 

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

Inductive LocalFields100I := | ι1000 | ι1001 . 
Definition LocalState100L := [ LocalState1000LRecord ; LocalState1001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState100L LocalFields100I . 
Opaque LocalState100LRecord . 

Inductive LocalFields101I := | ι1010 | ι1011 . 
Definition LocalState101L := [ LocalState1010LRecord ; LocalState1011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState101L LocalFields101I . 
Opaque LocalState101LRecord . 

Inductive LocalFields00I := | ι000 | ι001 . 
Definition LocalState00L := [ LocalState000LRecord ; LocalState001LRecord ] . 
GlobalGeneratePruvendoRecord LocalState00L LocalFields00I . 
Opaque LocalState00LRecord . 

Inductive LocalFields01I := | ι010 | ι011 . 
Definition LocalState01L := [ LocalState010LRecord ; LocalState011LRecord ] . 
GlobalGeneratePruvendoRecord LocalState01L LocalFields01I . 
Opaque LocalState01LRecord . 

Inductive LocalFields10I := | ι100 | ι101 . 
Definition LocalState10L := [ LocalState100LRecord ; LocalState101LRecord ] . 
GlobalGeneratePruvendoRecord LocalState10L LocalFields10I . 
Opaque LocalState10LRecord . 

Inductive LocalFields0I := | ι00 | ι01 . 
Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0L LocalFields0I . 
Opaque LocalState0LRecord . 

Inductive LocalFields1I := | ι10 | ι11 . 
Definition LocalState1L := [ LocalState10LRecord ; LocalState11000LRecord ] . 
GlobalGeneratePruvendoRecord LocalState1L LocalFields1I . 
Opaque LocalState1LRecord . 

Inductive LocalFieldsI := | ι0 | ι1 . 
Definition LocalStateL := [ LocalState0LRecord ; LocalState1LRecord ] . 
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
LocalState10010LRecord
LocalState10011LRecord
LocalState10100LRecord
LocalState10101LRecord
LocalState10110LRecord
LocalState10111LRecord
LocalState11000LRecord

LocalState0000LRecord
LocalState0001LRecord
LocalState0010LRecord
LocalState0011LRecord
LocalState0100LRecord
LocalState0101LRecord
LocalState0110LRecord
LocalState0111LRecord
LocalState1000LRecord
LocalState1001LRecord
LocalState1010LRecord
LocalState1011LRecord

LocalState000LRecord
LocalState001LRecord
LocalState010LRecord
LocalState011LRecord
LocalState100LRecord
LocalState101LRecord

LocalState00LRecord
LocalState01LRecord
LocalState10LRecord
LocalState1LRecord

LocalState0LRecord.
Transparent LocalStateLRecord.
Notation LocalStateField := (LocalStateField XHMap LocalStateLRecord).
#[global, program] Instance LocalStateField00000 : LocalStateField ( uint64).
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

#[global, program] Instance LocalStateField00001 : LocalStateField ( uint8).
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

#[global, program] Instance LocalStateField00010 : LocalStateField ( optional  (tuple ( uint64)( (UpdateRequestLRecord) ) )).
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

#[global, program] Instance LocalStateField00011 : LocalStateField ( boolean).
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

#[global, program] Instance LocalStateField00100 : LocalStateField ((UpdateRequestLRecord)).
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

#[global, program] Instance LocalStateField00101 : LocalStateField ( uint32).
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

#[global, program] Instance LocalStateField00110 : LocalStateField ( slice_).
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

#[global, program] Instance LocalStateField00111 : LocalStateField ( optional  ( uint256[] )).
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

#[global, program] Instance LocalStateField01000 : LocalStateField ( TvmCell).
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

#[global, program] Instance LocalStateField01001 : LocalStateField ( uint256[]).
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

#[global, program] Instance LocalStateField01010 : LocalStateField ((UpdateRequestLRecord[])).
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

#[global, program] Instance LocalStateField01011 : LocalStateField ( builder_).
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

#[global, program] Instance LocalStateField01100 : LocalStateField ( optional  ((UpdateRequestLRecord) )).
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

#[global, program] Instance LocalStateField01101 : LocalStateField ( optional  ( TvmCell )).
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

#[global, program] Instance LocalStateField01110 : LocalStateField ( uint256).
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

#[global, program] Instance LocalStateField01111 : LocalStateField ( optional  ( uint256 )).
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
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1000). 
eapply TransEmbedded. eapply (_ ι10000).
eapply (LocalState10000LEmbeddedType ι100001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1000). 
eapply TransEmbedded. eapply (_ ι10000).
eapply (LocalState10000LEmbeddedType ι100000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField10000 : typeclass_instances. 

#[global, program] Instance LocalStateField10001 : LocalStateField ( optional  ( uint32 )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1000). 
eapply TransEmbedded. eapply (_ ι10001).
eapply (LocalState10001LEmbeddedType ι100011). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1000). 
eapply TransEmbedded. eapply (_ ι10001).
eapply (LocalState10001LEmbeddedType ι100010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField10001 : typeclass_instances. 

#[global, program] Instance LocalStateField10010 : LocalStateField ((CustodianInfoLRecord[])).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1001). 
eapply TransEmbedded. eapply (_ ι10010).
eapply (LocalState10010LEmbeddedType ι100101). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1001). 
eapply TransEmbedded. eapply (_ ι10010).
eapply (LocalState10010LEmbeddedType ι100100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField10010 : typeclass_instances. 

#[global, program] Instance LocalStateField10011 : LocalStateField ((TransactionLRecord)).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1001). 
eapply TransEmbedded. eapply (_ ι10011).
eapply (LocalState10011LEmbeddedType ι100111). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1001). 
eapply TransEmbedded. eapply (_ ι10011).
eapply (LocalState10011LEmbeddedType ι100110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField10011 : typeclass_instances. 

#[global, program] Instance LocalStateField10100 : LocalStateField ((TransactionLRecord[])).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1010). 
eapply TransEmbedded. eapply (_ ι10100).
eapply (LocalState10100LEmbeddedType ι101001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1010). 
eapply TransEmbedded. eapply (_ ι10100).
eapply (LocalState10100LEmbeddedType ι101000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField10100 : typeclass_instances. 

#[global, program] Instance LocalStateField10101 : LocalStateField ( optional  ((TransactionLRecord) )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1010). 
eapply TransEmbedded. eapply (_ ι10101).
eapply (LocalState10101LEmbeddedType ι101011). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1010). 
eapply TransEmbedded. eapply (_ ι10101).
eapply (LocalState10101LEmbeddedType ι101010). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField10101 : typeclass_instances. 

#[global, program] Instance LocalStateField10110 : LocalStateField ( uint128).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1011). 
eapply TransEmbedded. eapply (_ ι10110).
eapply (LocalState10110LEmbeddedType ι101101). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1011). 
eapply TransEmbedded. eapply (_ ι10110).
eapply (LocalState10110LEmbeddedType ι101100). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField10110 : typeclass_instances. 

#[global, program] Instance LocalStateField10111 : LocalStateField ( optional  (tuple ( uint64)( (TransactionLRecord) ) )).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1011). 
eapply TransEmbedded. eapply (_ ι10111).
eapply (LocalState10111LEmbeddedType ι101111). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1011). 
eapply TransEmbedded. eapply (_ ι10111).
eapply (LocalState10111LEmbeddedType ι101110). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField10111 : typeclass_instances. 

#[global, program] Instance LocalStateField11000 : LocalStateField ( address).
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι11). 

eapply (LocalState11000LEmbeddedType ι110001). 
Defined.
Next Obligation. 
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι11). 

eapply (LocalState11000LEmbeddedType ι110000). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField11000 : typeclass_instances. 