Language-Defined Aspects and Attributes (Annex K)
=================================================

Language-Defined Aspects
------------------------

.. _tu-fe-language_defined_aspects-01:

1. The following aspects are in |SPARK| all other aspects are ignored???

.. _etu-language_defined_aspects:

.. todo:: Complete this section

.. _language_defined_attributes:

Language-Defined Attributes
---------------------------

.. _tu-fe-language_defined_attributes-01:

1. The following attributes are in |SPARK| no other Ada language
   defined attributes are in SPARK:

::

    Attribute       Allowed in SPARK 2014				Comment
    --------------------------------------------------------------------------------------------------------
    P'Access		X						No access types
    X'Access	    	X	
    X'Address	    	Only allowed within a representation clause	
    S'Adjacent	    	X	
    S'Aft		?	
    S'Alignment	    	Only allowed within a representation clause	
    X'Alignment	    	Only allowed within a representation clause	
    S'Base		Y	
    S'Bit_Order	    	Only allowed within a representation clause	
    P'Body_Version 	Y	
    T'Callable	    	X						No tasking
    E'Caller	    	X						No tasking
    S'Ceiling	    	Y	
    S'Class		X						No tagged types
    X'Component_Size    Y						probably
    S'Compose	    	X	
    A'Constrained	Y	
    S'Copy_Sign	    	Y						possibly limited at first
    E'Count		X						No tasking
    S'Definite	    	Y	
    S'Delta		?	
    S'Denorm	    	Y						Not supported at the moment
    S'Digits	    	Y	
    S'Exponent	    	X	
    S'External_Tag	X						No tagged types
    A'First		Y	
    S'First	 	Y	
    A'First(N)	    	Y	
    R.C'First_Bit	Only allowed within a representation clause	
    S'First_Valid	Y	
    S'Floor		Y	
    S'Fore		?	
    S'Fraction	    	X	
    X'Has_Same_Storage  X	
    E'Identity	    	?	
    T'Identity	    	X						No tasking
    S'Image		Y	
    S'Class'Input	X						No tagged types and no streams
    S'Input		X						No streams
    A'Last		Y	
    S'Last		Y	
    A'Last(N)	    	Y	
    R.C'Last_Bit	Only allowed within a representation clause	
    S'Last_Valid	Y	
    S'Leading_Part	X						As 'Exponent is not supported
    A'Length	    	Y	
    A'Length(N)	    	Y
    X'Loop_Entry        Y	
    S'Machine	    	Y						What use is this?
    S'Machine_Emax	Y	
    S'Machine_Emin	Y	
    S'Machine_Mantissa  Y	
    S'Machine_Overflows Y	
    S'Machine_Radix	Y	
    S'Machine_Rounding  Y	
    S'Machine_Rounds    Y	
    S'Max		Y	
    S'Max_Alignment_For_Allocation X					No access type
    S'Max_Size_In_Storage_Elements X					No access type
    S'Min		Y	
    S'Mod		Y	
    S'Model		???	
    S'Model_Emin	???	
    S'Model_Epsilon	???	
    S'Model_Mantissa	???	
    S'Model_Small	???	
    S'Modulus	   	Y	
    X'Old		Y	
    S'Class'Output	X						No tagged types and no streams
    S'Output	   	X						No streams
    X'Overlaps_Storage 	X	
    D'Partition_Id	Y	
    S'Pos		Y	
    R.C'Position	Only allowed within a representation clause	
    S'Pred		Y		       	 			In short term not for floats
    P'Priority	   	X						No tasking
    A'Range		Y	
    S'Range		Y	
    A'Range(N)	   	Y	
    S'Class'Read	X						No tagged types
    S'Read		X						No streams
    S'Remainder	   	Y	
    F'Result	   	Y	
    S'Round		?						Are we supporting decimal fixed points?
    S'Rounding	   	Y	
    S'Safe_First	???	
    S'Safe_Last	    	???	
    S'Scale		?						Are we supporting decimal fixed points?
    S'Scaling	   	?	
    S'Size		Only allowed within a representation clause	Possibly allowed in expressions later
    X'Size		Only allowed within a representation clause	Possibly allowed in expressions later
    S'Small		Y	
    S'Storage_Pool	X						No access types
    S'Storage_Size	X						No access types
    T'Storage_Size	X						No tasking
    S'Stream_Size	X						No streams
    S'Succ		Y	
    S'Tag		X						No tagged types
    X'Tag		X						No tagged types
    T'Terminated	X						No tasking
    S'Truncation	Y	
    S'Unbiased_Rounding Y	
    X'Unchecked_Access  X						No access types or aliases
    X'Update            Y
    S'Val		Y	
    X'Valid		Y						First release does not use this in proofs
    S'Value		Y	
    P'Version	  	Y	
    S'Wide_Image	Y	
    S'Wide_Value	Y	
    S'Wide_Wide_Image 	Y	
    S'Wide_Wide_Value 	Y	
    S'Wide_Wide_Width	Y	
    S'Wide_Width	Y	
    S'Width		Y	
    S'Class'Write	X						No tagged types
    S'Write		X						No streams

.. _etu-language_defined_attributes:

.. todo:: Complete this section
