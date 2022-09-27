
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
Require Export UrsusContractCreator.UrsusDefinitions.
Require Export UrsusContractCreator.ReverseTranslatorConstructions.

Require Import UMLang.UrsusLib.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.
(* Require Import UMLang.LocalClassGenerator.ClassGenerator. *)
Require Import multisig2.
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

Set Typeclasses Depth 100.





Inductive LocalFields0000I := | ι00000 | ι00001 .
Definition LocalState0000L := [( XHMap (string*nat) ( XMaybe  (XProd ( uint64)( UpdateRequestLRecord ) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState0000L LocalFields0000I . 
Opaque LocalState0000LRecord . 
Inductive LocalFields0001I := | ι00010 | ι00011 .
Definition LocalState0001L := [( XHMap (string*nat) ( boolean)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState0001L LocalFields0001I . 
Opaque LocalState0001LRecord . 
Inductive LocalFields0010I := | ι00100 | ι00101 .
Definition LocalState0010L := [( XHMap (string*nat) ( uint64)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState0010L LocalFields0010I . 
Opaque LocalState0010LRecord . 
Inductive LocalFields0011I := | ι00110 | ι00111 .
Definition LocalState0011L := [( XHMap (string*nat) (UpdateRequestLRecord)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState0011L LocalFields0011I . 
Opaque LocalState0011LRecord . 
Inductive LocalFields0100I := | ι01000 | ι01001 .
Definition LocalState0100L := [( XHMap (string*nat) ( XMaybe  (UpdateRequestLRecord ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState0100L LocalFields0100I . 
Opaque LocalState0100LRecord . 
Inductive LocalFields0101I := | ι01010 | ι01011 .
Definition LocalState0101L := [( XHMap (string*nat) ( uint8)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState0101L LocalFields0101I . 
Opaque LocalState0101LRecord . 
Inductive LocalFields0110I := | ι01100 | ι01101 .
Definition LocalState0110L := [( XHMap (string*nat) ( uint256)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState0110L LocalFields0110I . 
Opaque LocalState0110LRecord . 
Inductive LocalFields0111I := | ι01110 | ι01111 .
Definition LocalState0111L := [( XHMap (string*nat) ( TransactionLRecord)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState0111L LocalFields0111I . 
Opaque LocalState0111LRecord . 
Inductive LocalFields1000I := | ι10000 | ι10001 .
Definition LocalState1000L := [( XHMap (string*nat) ( XMaybe  ( TransactionLRecord ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState1000L LocalFields1000I . 
Opaque LocalState1000LRecord . 
Inductive LocalFields1001I := | ι10010 | ι10011 .
Definition LocalState1001L := [( XHMap (string*nat) ( XMaybe  (XProd ( uint64)(  TransactionLRecord ) ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState1001L LocalFields1001I . 
Opaque LocalState1001LRecord . 
Inductive LocalFields1010I := | ι10100 | ι10101 .
Definition LocalState1010L := [( XHMap (string*nat) ( uint128)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState1010L LocalFields1010I . 
Opaque LocalState1010LRecord . 
Inductive LocalFields1011I := | ι10110 | ι10111 .
Definition LocalState1011L := [( XHMap (string*nat) ( XMaybe  ( uint8 ))) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState1011L LocalFields1011I . 
Opaque LocalState1011LRecord . 
Inductive LocalFields1100I := | ι11000 | ι11001 .
Definition LocalState1100L := [( XHMap (string*nat) ( uint32)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState1100L LocalFields1100I . 
Opaque LocalState1100LRecord . 
(**************** LocalState Tree ***************.
   /\
  /\/\
 /\/\/\\
/\/\/\/\/\/\\
**************** LocalState Tree ***************)

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
Definition LocalState1L := [ LocalState10LRecord ; LocalState1100LRecord ] . 
GlobalGeneratePruvendoRecord LocalState1L LocalFields1I . 
Opaque LocalState1LRecord . 

Inductive LocalFieldsI := | ι0 | ι1 . 
Definition LocalStateL := [ LocalState0LRecord ; LocalState1LRecord ] . 
GlobalGeneratePruvendoRecord LocalStateL LocalFieldsI .
Opaque LocalStateLRecord . 


Transparent

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
LocalState1100LRecord

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

        #[global, program] Instance LocalStateField0000 : LocalStateField ( XMaybe  (XProd ( uint64)( UpdateRequestLRecord ) )).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000).
        eapply (LocalState0000LEmbeddedType ι00001). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0000).
        eapply (LocalState0000LEmbeddedType ι00000). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField0000 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField0001 : LocalStateField ( boolean).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001).
        eapply (LocalState0001LEmbeddedType ι00011). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000). 
eapply TransEmbedded. eapply (_ ι0001).
        eapply (LocalState0001LEmbeddedType ι00010). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField0001 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField0010 : LocalStateField ( uint64).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010).
        eapply (LocalState0010LEmbeddedType ι00101). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0010).
        eapply (LocalState0010LEmbeddedType ι00100). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField0010 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField0011 : LocalStateField (UpdateRequestLRecord).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011).
        eapply (LocalState0011LEmbeddedType ι00111). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001). 
eapply TransEmbedded. eapply (_ ι0011).
        eapply (LocalState0011LEmbeddedType ι00110). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField0011 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField0100 : LocalStateField ( XMaybe  (UpdateRequestLRecord )).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100).
        eapply (LocalState0100LEmbeddedType ι01001). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0100).
        eapply (LocalState0100LEmbeddedType ι01000). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField0100 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField0101 : LocalStateField ( uint8).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101).
        eapply (LocalState0101LEmbeddedType ι01011). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010). 
eapply TransEmbedded. eapply (_ ι0101).
        eapply (LocalState0101LEmbeddedType ι01010). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField0101 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField0110 : LocalStateField ( uint256).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110).
        eapply (LocalState0110LEmbeddedType ι01101). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0110).
        eapply (LocalState0110LEmbeddedType ι01100). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField0110 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField0111 : LocalStateField ( TransactionLRecord).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111).
        eapply (LocalState0111LEmbeddedType ι01111). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011). 
eapply TransEmbedded. eapply (_ ι0111).
        eapply (LocalState0111LEmbeddedType ι01110). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField0111 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField1000 : LocalStateField ( XMaybe  ( TransactionLRecord )).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1000).
        eapply (LocalState1000LEmbeddedType ι10001). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1000).
        eapply (LocalState1000LEmbeddedType ι10000). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField1000 : typeclass_instances. 
        

#[global, program] Instance LocalStateField1001 : LocalStateField ( XMaybe  (XProd ( uint64)( TransactionLRecord ) )).
Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1001).
        eapply (LocalState1001LEmbeddedType ι10011). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100). 
eapply TransEmbedded. eapply (_ ι1001).
        eapply (LocalState1001LEmbeddedType ι10010). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField1001 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField1010 : LocalStateField ( uint128).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1010).
        eapply (LocalState1010LEmbeddedType ι10101). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1010).
        eapply (LocalState1010LEmbeddedType ι10100). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField1010 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField1011 : LocalStateField ( XMaybe  ( uint8 )).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1011).
        eapply (LocalState1011LEmbeddedType ι10111). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101). 
eapply TransEmbedded. eapply (_ ι1011).
        eapply (LocalState1011LEmbeddedType ι10110). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField1011 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField1100 : LocalStateField ( uint32).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι11). 

        eapply (LocalState1100LEmbeddedType ι11001). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι11). 

        eapply (LocalState1100LEmbeddedType ι11000). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField1100 : typeclass_instances. 
        