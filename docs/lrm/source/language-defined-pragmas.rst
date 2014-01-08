.. _language_defined_pragmas:

Language-Defined Pragmas (Annex L)
==================================

.. _tu-fe-language_defined_pragmas-01:

1. The following Ada language-defined pragmas are supported as follows:

============================= ====================== ===============================================
Pragma                        Allowed in SPARK 2014  Comment
============================= ====================== ===============================================
All_Calls_Remote	      No
Assert             	      Yes
Assertion_Policy	      Yes
Asynchronous       	      No
Atomic          	      Yes
Atomic_Components  	      Yes
Attach_Handler     	      No		     No tasking
Convention         	      Yes
CPU             	      No		     No tasking
Default_Storage_Pool   	      No		     No access types
Detect_Blocking	  	      No		     No tasking
Discard_Names 	  	      No
Dispatching_Domain 	      No		     No tasking
Elaborate          	      Yes
Elaborate_All      	      Yes
Elaborate_Body     	      Yes
Export             	      Yes
Import             	      Yes
Independent        	      Yes
Independent_Components 	      Yes
Inline             	      Yes
Inspection_Point   	      Yes
Interrupt_Handler  	      No		     No tasking
Interrupt_Priority 	      No		     No tasking
Linker_Options     	      Yes
List               	      Yes
Locking_Policy    	      No		     No tasking
No_Return          	      Yes
Normalize_Scalars  	      Yes
Optimize           	      Yes
Pack              	      Yes
Page               	      Yes
Partition_Elaboration_Policy  Yes
Preelaborable_Initialization  Yes
Preelaborate       	      Yes
Priority  	  	      No		     No tasking
Priority_Specific_Dispatching No  		     No tasking
Profile            	      Yes
Pure               	      Yes
Queuing_Policy 	 	      No		     No Tasking
Relative_Deadline  	      No		     No Tasking
Remote_Call_Interface 	      No		     Distributed systems
Remote_Types 	 	      No		     Distributed systems
Restrictions 	 	      Yes
Reviewable         	      Yes
Shared_Passive     	      No                     Distributed systems
Storage_Size 	 	      No		     No tasking
Suppress           	      Yes
Task_Dispatching_Policy       No		     No tasking
Unchecked_Union	 	      No
Unsuppress 	  	      Yes
Volatile           	      Yes
Volatile_Components 	      No
============================= ====================== ===============================================


.. _tu-fe-language_defined_pragmas-02:

2. The following |SPARK| language-defined pragmas are defined:

============================= ====================== =================================================
Pragma                        Allowed in SPARK 2014  Comment
============================= ====================== =================================================
Abstract_State	 	      Yes
Assert_And_Cut	 	      Yes
Assume		 	      Yes
Assume_No_Invalid_Values      Yes
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
Refined_Post 	 	      Yes
Refined_State 	 	      Yes
SPARK_Mode         	      Yes                    Language defined but implementation dependent
============================= ====================== =================================================

.. _tu-fe-language_defined_pragmas-03:

3. The following GNAT implementation-defined pragmas are permitted in |SPARK|:

============================= ====================== =================================================
Pragma                        Allowed in SPARK 2014  Comment
============================= ====================== =================================================
Ada_83			      Yes
Ada_95			      Yes
Ada_05			      Yes
Ada_2005		      Yes
Ada_12             	      Yes
Ada_2012           	      Yes
Annotate		      Yes
Check	 		      Yes
Check_Policy 		      Yes
Debug			      Yes		     Ignored (replaced by null statement)
Inline_Always      	      Yes
Pure_Function      	      Yes
Restriction_Warnings  	      Yes
Style_Checks      	      Yes
Test_Case          	      Yes
Warnings           	      Yes
============================= ====================== =================================================

.. _etu-language_defined_pragmas:

