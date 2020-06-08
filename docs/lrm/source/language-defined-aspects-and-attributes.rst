Language-Defined Aspects and Attributes (Annex K)
=================================================

Language-Defined Aspects
------------------------


1. Ada language aspects are permitted as shown in the following table:

============================= ====================== ===============================================
Aspect                        Allowed in SPARK 2014  Comment
============================= ====================== ===============================================
Address	    		      Yes
Alignment (object)	      Yes
Alignment (subtype)	      Yes
All_Calls_Remote	      No
Asynchronous       	      No
Atomic          	      Yes
Atomic_Components  	      Yes
Attach_Handler     	      Yes
Bit_Order		      Yes
Coding			      Yes
Component_Size		      Yes
Constant_Indexing	      No
Convention         	      Yes
CPU             	      Yes
Default_Component_Value	      Yes
Default_Iterator	      No
Default_Storage_Pool	      No
Default_Value		      Yes
Default_Storage_Pool   	      No		     Restricted access types
Dispatching_Domain 	      No		     Ravenscar
Dynamic_Predicate             Yes
Elaborate_Body     	      Yes
Export             	      Yes
External_Name		      Yes
External_Tag		      No		     No tags
Implicit_Dereference	      No		     Restricted access types
Import             	      Yes
Independent        	      Yes
Independent_Components 	      Yes
Inline             	      Yes
Interrupt_Handler  	      Yes
Interrupt_Priority 	      Yes
Iterator_Element	      No
Layout (record)		      Yes
Link_Name     	      	      Yes
Machine_Radix		      Yes
No_Return          	      Yes
Output			      No		     No streams
Pack              	      Yes
Pre			      Yes
Pre'Class		      Yes
Post			      Yes
Post'Class		      Yes
Predicate_Failure	      Yes
Preelaborate       	      Yes
Priority  	  	      Yes
Pure               	      Yes
Relative_Deadline	      Yes
Remote_Call_Interface	      No
Remote_Types		      No
Shared_Passive		      No
Size (object)		      Yes
Size (subtype)		      Yes
Small			      Yes
Static_Predicate	      Yes
Storage_Pool		      No		     Restricted access types
Storage_Size (access)         No		     Restricted access types
Storage_Size (task)	      Yes
Stream_Size  		      No		     No streams
Synchronization		      Yes
Type_Invariant		      Yes
Type_Invariant'Class	      No
Unchecked_Union		      Yes
Variable_Indexing	      No
Volatile           	      Yes
Volatile_Components 	      Yes
Write			      No		     No streams
============================= ====================== ===============================================


2. |SPARK| defines the following aspects:

============================= ====================== =================================================
Aspect                        Allowed in SPARK 2014  Comment
============================= ====================== =================================================
Abstract_State	 	      Yes
Async_Readers		      Yes
Async_Writers		      Yes
Constant_After_Elaboration    Yes
Contract_Cases     	      Yes
Default_Initial_Condition     Yes
Depends		 	      Yes
Depends'Class	 	      Yes
Effective_Reads		      Yes
Effective_Writes	      Yes
Extensions_Visible            Yes
Ghost                         Yes
Global		 	      Yes
Global'Class	 	      Yes
Initial_Condition  	      Yes
Initializes	  	      Yes
Part_Of			      Yes
Refined_Depends    	      Yes
Refined_Global	 	      Yes
Refined_Post		      Yes
Refined_State 	 	      Yes
SPARK_Mode		      Yes		     Language defined but implementation dependent
Volatile_Function             Yes
============================= ====================== =================================================


.. todo:: Complete this section

.. _language_defined_attributes:

Language-Defined Attributes
---------------------------


1. The following attributes are in |SPARK|.

===================================== ====================== ====================================================
Attribute                              Allowed in SPARK 2014 Comment
===================================== ====================== ====================================================
P'Access			      No		     Restricted access types
X'Access	    		      Yes
X'Address	    		      No                     Only allowed in representation clauses
S'Adjacent	    		      Yes                    Implicit precondition (Ada RM A.5.3(50))
S'Aft				      Yes
S'Alignment	    		      Warn                   Warning in pedantic mode
X'Alignment	    		      Warn		     Warning in pedantic mode
S'Base				      Yes
S'Bit_Order	    		      Warn		     Warning in pedantic mode
P'Body_Version 			      Yes
T'Callable	    		      Yes
E'Caller	    		      Yes
S'Ceiling	    		      Yes
S'Class				      Yes
X'Component_Size    		      Warn     		     Warning in pedantic mode
S'Compose	    		      No
A'Constrained			      Yes
S'Copy_Sign	    		      Yes
E'Count				      No
S'Definite	    		      Yes
S'Delta				      Yes
S'Denorm	    		      Yes
S'Digits	    		      Yes
S'Exponent	    		      No
S'External_Tag			      No	             No tags
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
T'Identity	    		      Yes
X'Image				      Yes                    Same as S'Image(X) (Ada RM 3.5(55.4/4))
S'Image				      Yes
S'Class'Input			      No		     No streams
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
S'Max_Alignment_For_Allocation 	      No	             Restricted access types
S'Max_Size_In_Storage_Elements 	      No		     Restricted access types
S'Min				      Yes
S'Mod				      Yes
S'Model				      Yes
S'Model_Emin			      Yes
S'Model_Epsilon			      Yes
S'Model_Mantissa		      Yes
S'Model_Small			      Yes
S'Modulus	   		      Yes
X'Old				      Yes
S'Class'Output			      No		     No streams
S'Output	   		      No		     No streams
X'Overlaps_Storage 		      No
D'Partition_Id			      Yes
S'Pos				      Yes
R.C'Position			      Warn                   Warning in pedantic mode
S'Pred				      Yes                    Implicit precondition (Ada RM 3.5(27))
P'Priority	   		      No                     Ravenscar
A'Range				      Yes
S'Range				      Yes
A'Range(N)	   		      Yes
S'Class'Read			      No		     No streams
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
S'Storage_Pool			      No		     Restricted access types
S'Storage_Size			      No		     Restricted access types
T'Storage_Size			      Yes
S'Stream_Size			      No		     No streams
S'Succ				      Yes                    Implicit precondition (Ada RM 3.5(24))
S'Tag				      No		     No tags
X'Tag				      No		     No tags
T'Terminated			      Yes
System'To_Address 		      Yes
S'Truncation			      Yes
S'Truncation			      Yes
X'Unchecked_Access  		      No
X'Update            		      Yes
S'Val				      Yes                    Implicit precondition (Ada RM 3.5.5(7))
X'Valid				      Yes	             Assumed to be True at present
S'Value				      Yes                    Implicit precondition (Ada RM 3.5(55/3))
P'Version	  		      Yes
S'Wide_Image			      Yes
S'Wide_Value			      Yes                    Implicit precondition (Ada RM 3.5(43/3))
S'Wide_Wide_Image 		      Yes
S'Wide_Wide_Value 		      Yes                    Implicit precondition (Ada RM 3.5(39.12/3))
S'Wide_Wide_Width		      Yes
S'Wide_Width			      Yes
S'Width				      Yes
S'Class'Write			      No		     No streams
S'Write				      No		     No streams
===================================== ====================== ====================================================


GNAT Implementation-Defined Attributes
--------------------------------------

The following GNAT implementation-defined attributes are permitted in |SPARK|:

===================================== ====================== ====================================================
Attribute                              Allowed in SPARK 2014 Comment
===================================== ====================== ====================================================
X'Img                                 Yes                    Same as X'Image (Ada RM 3.5(55.4/4))
===================================== ====================== ====================================================
