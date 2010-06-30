package Derived_Type is

   type Counter is new Positive;
   type Index_Int is new Integer range 1 .. 10;
   type Index_Real is new Float range 1.0 .. 10.0;

   procedure Affect
     (Index_In : out Index_Int;
      Index_Re : out Index_Real);

end Derived_Type;
