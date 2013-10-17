.. _language_defined_pragmas:

Language-Defined Pragmas (Annex L)
==================================

.. _tu-fe-language_defined_pragmas-01:

1. The following Ada language defined pragmas are supported as follows:

============================= ====================== ===============================================
Pragma                        Allowed in SPARK 2014  Comment
============================= ====================== ===============================================
All_Calls_Remote	      No
Assert             	      Yes
Assertion_Policy	      Yes
Asynchronous       	      No
Atomic          	      Yes
Atomic_Components  	      ?
Attach_Handler     	      No
Convention         	      Yes
CPU             	      No		     No tasking
Default_Storage_Pool   	      No		     No access types
Detect_Blocking	  	      No		     No tasking
Discard_Names 	  	      No
Dispatching_Domain 	      No
Elaborate          	      Yes
Elaborate_All      	      Yes
Elaborate_Body     	      Yes
Export             	      Yes
Import             	      Yes
Independent        	      ?
Independent_Components 	      ?
Inline             	      Yes
Inspection_Point   	      Warn		     Warning otherwise ignored?
Interrupt_Handler  	      No		     No tasking
Interrupt_Priority 	      No		     No tasking
Linker_Options     	      Warn             	     Warning otherwise ignored?
List               	      Warn             	     Warning otherwise ignored?
Locking_Policy    	      No		     No tasking
No_Return          	      ?             	     I thought we were going to support these?
Normalize_Scalars  	      No            	     No support for invalid values
Optimise           	      Warn             	     Warning otherwise ignored?
Pack              	      Yes
Page               	      Warn		     Warning otherwise ignored?
Partition_Elaboration_Policy  ?   		     Partition wide would it appear in a compilation unit?
Preelaborable_Initialization  Yes
Preelaborate       	      Yes
Priority  	  	      No		     No tasking
Priority_Specific_Dispatching No  		     No tasking
Profile            	      ?  	             Probably required
Pure               	      Y
Queuing_Policy 	 	      No		     No Tasking
Relative_Deadline  	      No		     No Tasking
Remote_Call_Interface 	      ?
Remote_Types 	 	      ?
Restrictions 	 	      ?			     Does this apply to a partition?
Reviewable         	      Warn	    	     Warning otherwise ignored?
Shared_Passive     	      ?
Storage_Size 	 	      No		     No tasking
Suppress           	      ?			     Would this also supress the proof check?
Task_Dispatching_Policy       No		     No tasking
Unchecked_Union	 	      No    		     I think we ruled this out
Unsuppress 	  	      ?
Volatile           	      Yes
Volatile_Components 	      No
============================= ====================== ===============================================


.. _tu-fe-language_defined_pragmas-02:

2. The following |SPARK| language pragmas are defined:

============================= ====================== =================================================
Pragma                        Allowed in SPARK 2014  Comment
============================= ====================== =================================================
Abstract_State	 	      Yes
Assert_And_Cut	 	      Yes
Assume		 	      Yes
Assume_No_Invalid_Values      Yes		     With ability to state particular variable or type
Async_Readers		      Yes
Async_Writers		      Yes
Contract_Cases     	      Yes
Depends		 	      Yes
Effective_Reads		      Yes
Effective_Writes	      Yes
Global		 	      Yes
Initializes	  	      Yes
Initial_Condition  	      Yes
Loop_Invariant	 	      Yes
Loop_Variant	  	      Yes
Part_Of			      Yes
Post		  	      Yes
Pre		  	      Yes
Refined_Depends    	      Yes
Refined_Global	 	      Yes
Refined_State 	 	      Yes
============================= ====================== =================================================

.. _tu-fe-language_defined_pragmas-03:

3. The following pragmas to go in |SPARK| UG?  SPARK 2014
   Implementation Defined Pragmas:

============================= ====================== =================================================
Pragma                        Allowed in SPARK 2014  Comment
============================= ====================== =================================================
Annotate		      Yes	
SPARK_Mode         	      Yes
Restriction_Warnings  	      ?			     We amy need this for SPARK profiles
Test_Case          	      Yes
Warnings           	      Yes
============================= ====================== =================================================

.. _tu-fe-language_defined_pragmas-04:

4. Gnat defined pragmas to go in |SPARK| UG.  Gnat specific pragmas:

============================= ====================== =================================================
Pragma                        Allowed in SPARK 2014  Comment
============================= ====================== =================================================
Ada_83			      Yes
Ada_95			      Yes
Ada_05			      Yes
Ada_2005		      Yes
Ada_12             	      Yes
Ada_2012           	      Yes
Check	 		      Yes		     Is this used by SPARK in a specific way?
Check_Policy 		      Yes		     Is this used by SPARK in a specific way?
Inline_Always      	      Yes
Pure_Function      	      Yes
============================= ====================== =================================================


.. _etu-language_defined_pragmas:

What about other Gnat specific pragmas?

.. todo:: complete this section

