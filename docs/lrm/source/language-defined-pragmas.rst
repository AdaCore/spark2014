.. _language_defined_pragmas:

Language-Defined Pragmas (Annex L)
==================================

The following Ada language defined pragmas are supported as follows:

::

    pragma All_Calls_Remote	  X
    pragma Assert             	  Y
    pragma Assertion_Policy	  Y
    pragma Asynchronous       	  X
    pragma Atomic          	  Y
    pragma Atomic_Components  	  ?
    pragma Attach_Handler     	  X
    pragma Convention         	  Y
    pragma CPU             	  X		No tasking
    pragma Default_Storage_Pool   X 		No access types
    pragma Detect_Blocking	  X 		No tasking
    pragma Discard_Names 	  X
    pragma Dispatching_Domain 	  X
    pragma Elaborate          	  Y
    pragma Elaborate_All      	  Y
    pragma Elaborate_Body     	  Y
    pragma Export             	  Y
    pragma Import             	  Y
    pragma Independent        	  ?
    pragma Independent_Components ?
    pragma Inline             	  Y
    pragma Inspection_Point   	  W		Warning otherwise ignored?
    pragma Interrupt_Handler  	  X		No tasking
    pragma Interrupt_Priority 	  X		No tasking
    pragma Linker_Options     	  W             Warning otherwise ignored?
    pragma List               	  W             Warning otherwise ignored?
    pragma Locking_Policy    	  X 		No tasking
    pragma No_Return          	  ?             I thought we were going to support these?
    pragma Normalize_Scalars  	  X             No support for invalid values
    pragma Optimise           	  W             Warning otherwise ignored?
    pragma Pack              	  Y
    pragma Page               	  W             Warning otherwise ignored?
    pragma Partition_Elaboration_Policy ?   	Partition wide would it appear in a compilation unit?
    pragma Preelaborable_Initialization Y
    pragma Preelaborate       	 Y
    pragma Priority  	  	 X		No tasking
    pragma Priority_Specific_Dispatching X	No tasking
    pragma Profile            	 ?  	        Probably required
    pragma Pure               	 Y
    pragma Queuing_Policy 	 X		No Tasking
    pragma Relative_Deadline  	 Y		No Tasking
    pragma Remote_Call_Interface ?
    pragma Remote_Types 	 ?
    pragma Restrictions 	 ?		Does this apply to a partition?
    pragma Reviewable         	 ?		Warning otherwise ignored?
    pragma Shared_Passive     	 ?
    pragma Storage_Size 	 X		No tasking
    pragma Suppress           	 ?		Would this also supress the proof check?
    pragma Task_Dispatching_Policy X		No tasking
    pragma Unchecked_Union	 X    		I think we ruled this out
    pragma Unsuppress 	  	 ?
    pragma Volatile           	 Y
    pragma Volatile_Components 	 X


The following |SPARK| language pragmas are defined:

::

    pragma Abstract_State	 Y
    pragma Assert_And_Cut	 Y
    pragma Assume		 Y
    pragma Assume_No_Invalid_Values Y		Perhaps with an extension to state particular
    	   			    		variable or type
    pragma Contract_Cases     	 Y
    pragma Depends		 Y
    pragma Global		 Y
    pragma Initializes	  	 Y
    pragma Initial_Condition  	 Y
    pragma Loop_Invariant	 Y
    pragma Loop_Variant	  	 Y
    pragma Post		  	 Y
    pragma Pre		  	 Y
    pragma Refined_Depends    	 Y
    pragma Refined_Global	 Y
    pragma Refined_State 	 Y


The following pragmas to go in |SPARK| UG?
SPARK 2014 Implementation Defined Pragmas:

::

    pragma Annotate		 Y	
    pragma SPARK_Mode         	 Y
    pragma Restriction_Warnings  ?		We amy need this for SPARK profiles
    pragma Test_Case          	 Y
    pragma Warnings           	 Y

Gnat defined pragmas to go in |SPARK| UG. 
Gnat specific pragmas:

    pragma Ada_83		Y
    pragma Ada_95		Y
    pragma Ada_05		Y
    pragma Ada_2005		Y
    pragma Ada_12             	Y
    pragma_Ada_2012           	Y
    pragma Check	 	Y		Is this used by SPARK in a specific way?
    pragma Check_Policy 	Y		Is this used by SPARK in a specific way?
    pragma Inline_Always      	Y
    pragma Pure_Function      	Y


What about other Gnat specific pragmas?

.. todo:: complete this section

