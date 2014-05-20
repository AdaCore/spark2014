Language-Defined Aspects and Attributes (Annex K)
=================================================

Language-Defined Aspects
------------------------

.. _tu-fe-language_defined_aspects-01:

1. Ada language aspects are permitted as shown in the following table:

============================= ====================== ===============================================
Aspect                        Allowed in SPARK 2014  Comment
============================= ====================== ===============================================
Alignment (object)	      Yes
Alignment (subtype)	      Yes
All_Calls_Remote	      No
Asynchronous       	      No
Atomic          	      Yes
Atomic_Components  	      Yes
Attach_Handler     	      No                     No tasking
Bit_Order		      Yes
Coding			      Yes
Component_Size		      Yes
Constant_Indexing	      No
Convention         	      Yes
CPU             	      No		     No tasking
Default_Component_Value	      Yes
Default_Iterator	      No
Default_Storage_Pool	      No
Default_Value		      Yes
Default_Storage_Pool   	      No		     No access types
Detect_Blocking	  	      No		     No tasking
Dispatching_Domain 	      No		     No tasking
Elaborate_Body     	      Yes
Export             	      Yes
External_Name		      Yes
External_Tag		      No		     No tagged types
Implicit_Dereference	      No		     No access types
Import             	      Yes
Independent        	      Yes
Independent_Components 	      Yes
Inline             	      Yes
Interrupt_Handler  	      No		     No tasking
Interrupt_Priority 	      No		     No tasking
Iterator_Element	      No
Layout (record)		      Yes
Link_Name     	      	      Yes
Machine_Radix		      Yes
No_Return          	      Yes
Output			      No		     No streams
Pack              	      Yes
Pre			      Yes
Pre'Class		      No		     No tagged types
Post			      Yes
Post'Class		      No		     No tagged types
Preelaborate       	      Yes
Priority  	  	      No		     No tasking
Pure               	      Yes
Relative_Deadline	      No		     No tasking
Remote_Call_Interface	      No
Remote_Types		      No
Shared_Passive		      No		     No tasking
Size (object)		      Yes
Size (subtype)		      Yes
Small			      Yes
Static_Predicate	      Yes
Storage_Pool		      No		     No access types
Storage_Size (access)         No		     No access types
Storage_Size (task)	      No		     No tasking
Stream_Size  		      No		     No streams
Synchronization		      No		     No tasking
Type_Invariant		      No
Type_Invariant'Class	      No		     No tasking
Unchecked_Union		      No
Variable_Indexing	      No
Volatile           	      Yes
Volatile_Components 	      Yes
Write			      No		     No streams
============================= ====================== ===============================================

.. _tu-fe-language_defined_aspects-02:

2. |SPARK| defines the following aspects:

============================= ====================== =================================================
Aspect                        Allowed in SPARK 2014  Comment
============================= ====================== =================================================
Abstract_State	 	      Yes
Async_Readers		      Yes
Async_Writers		      Yes
Contract_Cases     	      Yes
Depends		 	      Yes
Effective_Reads		      Yes
Effective_Writes	      Yes
Global		 	      Yes
Initializes	  	      Yes
Initial_Condition  	      Yes
Part_Of			      Yes
Refined_Depends    	      Yes
Refined_Global	 	      Yes
Refined_Post		      Yes
Refined_State 	 	      Yes
SPARK_Mode		      Yes		     Language defined but implementation dependent
============================= ====================== =================================================

.. _etu-language_defined_aspects:

.. todo:: Complete this section

.. _language_defined_attributes:

Language-Defined Attributes
---------------------------

.. _tu-fe-language_defined_attributes-01:

1. The following attributes are in |SPARK|.

===================================== ====================== ====================================================
Attribute                              Allowed in SPARK 2014 Comment
===================================== ====================== ====================================================
P'Access			      No		     No access types
X'Access	    		      No
X'Address	    		      Warn		     Warning in pedantic mode
S'Adjacent	    		      Yes
S'Aft				      Yes
S'Alignment	    		      Warn                   Warning in pedantic mode
X'Alignment	    		      Warn		     Warning in pedantic mode
S'Base				      Yes
S'Bit_Order	    		      Warn		     Warning in pedantic mode
P'Body_Version 			      Yes
T'Callable	    		      No		     No tasking
E'Caller	    		      No	             No tasking
S'Ceiling	    		      Yes
S'Class				      No		     No tagged types
X'Component_Size    		      Warn     		     Warning in pedantic mode
S'Compose	    		      No
A'Constrained			      Yes
S'Copy_Sign	    		      Yes
E'Count				      No		     No tasking
S'Definite	    		      Yes
S'Delta				      Yes
S'Denorm	    		      Yes
S'Digits	    		      Yes
S'Exponent	    		      No
S'External_Tag			      No	             No tagged types
A'First				      Yes
S'First	 			      Yes
A'First(N)	    		      Yes
R.C'First_Bit			      Warn		     Warning in Pedantic mode
S'First_Valid			      Yes
S'Floor				      Yes
S'Fore				      Yes
S'Fraction	    		      No
X'Has_Same_Storage  		      No
E'Identity	    		      No
T'Identity	    		      No		     No tasking
S'Image				      Yes
S'Class'Input			      No		     No tagged types and no streams
S'Input				      No		     No streams
A'Last				      Yes
S'Last				      Yes
A'Last(N)	    		      Yes
R.C'Last_Bit			      Warn		     Warning in pedantic mode
S'Last_Valid			      Yes
S'Leading_Part			      No
A'Length	    		      Yes
A'Length(N)	    		      Yes
X'Loop_Entry        		      Yes
S'Machine	    		      Yes
S'Machine_Emax			      Yes
S'Machine_Emin			      Yes
S'Machine_Mantissa  		      Yes
S'Machine_Overflows 		      Yes
S'Machine_Radix			      Yes
S'Machine_Rounding  		      Yes
S'Machine_Rounds    		      Yes
S'Max				      Yes
S'Max_Alignment_For_Allocation 	      No	             No access types
S'Max_Size_In_Storage_Elements 	      No		     No access types
S'Min				      Yes
S'Mod				      Yes
S'Model				      Yes
S'Model_Emin			      Yes
S'Model_Epsilon			      Yes
S'Model_Mantissa		      Yes
S'Model_Small			      Yes
S'Modulus	   		      Yes
X'Old				      Yes
S'Class'Output			      No		     No tagged types and no streams
S'Output	   		      No		     No streams
X'Overlaps_Storage 		      No
D'Partition_Id			      Yes
S'Pos				      Yes
R.C'Position			      Warn                   Warning in pedantic mode
S'Pred				      Yes
P'Priority	   		      No		     No tasking
A'Range				      Yes
S'Range				      Yes
A'Range(N)	   		      Yes
S'Class'Read			      No		     No tagged types
S'Read				      No		     No streams
S'Remainder	   		      Yes
F'Result	   		      Yes
S'Round				      Yes
S'Rounding	   		      Yes
S'Safe_First			      Yes
S'Safe_Last	    		      Yes
S'Scale				      Yes
S'Scaling	   		      Yes
S'Size				      Warn                   Warning in pedantic
X'Size				      Warn     		     Warning in pedantic
S'Small				      Yes
S'Storage_Pool			      No		     No access types
S'Storage_Size			      No		     No access types
T'Storage_Size			      No		     No tasking
S'Stream_Size			      No		     No streams
S'Succ				      Yes
S'Tag				      No		     No tagged types
X'Tag				      No		     No tagged types
T'Terminated			      No		     No tasking
S'Truncation			      Yes
S'Unbiased_Rounding 		      Yes
X'Unchecked_Access  		      No		     No access types or aliases
X'Update            		      Yes
S'Val				      Yes
X'Valid				      Yes	             Assumed to be True at present
S'Value				      Yes
P'Version	  		      Yes
S'Wide_Image			      Yes
S'Wide_Value			      Yes
S'Wide_Wide_Image 		      Yes
S'Wide_Wide_Value 		      Yes
S'Wide_Wide_Width		      Yes
S'Wide_Width			      Yes
S'Width				      Yes
S'Class'Write			      No		     No tagged types
S'Write				      No		     No streams
===================================== ====================== ====================================================

.. _etu-language_defined_attributes:
