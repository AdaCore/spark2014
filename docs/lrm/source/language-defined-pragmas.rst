.. _language_defined_pragmas:

Language-Defined Pragmas (Annex L)
==================================

Ada Language-Defined Pragmas
----------------------------

.. _tu-fe-language_defined_pragmas-01:

The following Ada language-defined pragmas are supported as follows:

============================= ====================== ===============================================
Pragma                        Allowed in SPARK 2014  Comment
============================= ====================== ===============================================
All_Calls_Remote	      No
Assert             	      Yes
Assertion_Policy	      Yes                    No effect on provability (see section "Assertion Pragmas" in the SPARK User's Guide)
Asynchronous       	      No
Atomic          	      Yes
Atomic_Components  	      Yes
Attach_Handler     	      Yes
Convention         	      Yes
CPU             	      Yes
Default_Storage_Pool   	      No		     Restricted access types
Detect_Blocking	  	      Yes
Discard_Names 	  	      No
Dispatching_Domain 	      No		     Ravenscar
Elaborate          	      Yes
Elaborate_All      	      Yes
Elaborate_Body     	      Yes
Export             	      Yes
Import             	      Yes
Independent        	      Yes
Independent_Components 	      Yes
Inline             	      Yes
Inspection_Point   	      Yes
Interrupt_Handler  	      Yes
Interrupt_Priority 	      Yes
Linker_Options     	      Yes
List               	      Yes
Locking_Policy    	      Yes
No_Return          	      Yes
Normalize_Scalars  	      Yes
Optimize           	      Yes
Pack              	      Yes
Page               	      Yes
Partition_Elaboration_Policy  Yes                    Ravenscar
Preelaborable_Initialization  Yes
Preelaborate       	      Yes
Priority  	  	      Yes
Priority_Specific_Dispatching No                     Ravenscar
Profile            	      Yes
Pure               	      Yes
Queuing_Policy 	 	      Yes                    Ravenscar
Relative_Deadline  	      Yes
Remote_Call_Interface 	      No		     Distributed systems
Remote_Types 	 	      No		     Distributed systems
Restrictions 	 	      Yes
Reviewable         	      Yes
Shared_Passive     	      No                     Distributed systems
Storage_Size 	 	      Yes/No                 tasks, not access types
Suppress           	      Yes
Task_Dispatching_Policy       No		     Ravenscar
Unchecked_Union	 	      Yes
Unsuppress 	  	      Yes
Volatile           	      Yes
Volatile_Components 	      Yes
============================= ====================== ===============================================


|SPARK| Language-Defined Pragmas
--------------------------------

.. _tu-fe-language_defined_pragmas-02:

The following |SPARK| language-defined pragmas are defined:

============================= ====================== =================================================
Pragma                        Allowed in SPARK 2014  Comment
============================= ====================== =================================================
Abstract_State	 	      Yes
Assert_And_Cut	 	      Yes
Assume		 	      Yes
Async_Readers		      Yes
Async_Writers		      Yes
Constant_After_Elaboration    Yes
Contract_Cases     	      Yes
Default_Initial_Condition     Yes
Depends		 	      Yes
Effective_Reads		      Yes
Effective_Writes	      Yes
Extensions_Visible            Yes
Ghost                         Yes
Global		 	      Yes
Initial_Condition  	      Yes
Initializes	  	      Yes
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
Volatile_Function             Yes
============================= ====================== =================================================

GNAT Implementation-Defined Pragmas
-----------------------------------

.. _tu-fe-language_defined_pragmas-03:

The following GNAT implementation-defined pragmas are permitted in |SPARK|:

============================= ====================== =================================================
Pragma                        Allowed in SPARK 2014  Comment
============================= ====================== =================================================
Ada_83			      Yes
Ada_95			      Yes
Ada_05			      Yes
Ada_2005		      Yes
Ada_12             	      Yes
Ada_2012           	      Yes
Ada_2020           	      Yes
Annotate		      Yes
Check	 		      Yes
Check_Policy 		      Yes                    No effect on provability (see section "Assertion Pragmas" in the SPARK User's Guide)
Compile_Time_Error	      Yes		     Ignored (replaced by null statement)
Compile_Time_Warning	      Yes		     Ignored (replaced by null statement)
Debug			      Yes		     Ignored (replaced by null statement)
Default_Scalar_Storage_Order  Yes
Inline_Always      	      Yes
Linker_Section      	      Yes
Max_Queue_Length              Yes                    Extended Ravenscar
No_Elaboration_Code_All       Yes
No_Heap_Finalization          Yes
Overflow_Mode                 Yes
Predicate_Failure             Yes
Provide_Shift_Operators       Yes
Pure_Function      	      Yes
Restriction_Warnings  	      Yes
Secondary_Stack_Size          Yes
Style_Checks      	      Yes
Test_Case          	      Yes
Unmodified                    Yes
Unreferenced                  Yes
Unused                        Yes
Validity_Checks               Yes
Warnings           	      Yes
Weak_External          	      Yes
============================= ====================== =================================================
