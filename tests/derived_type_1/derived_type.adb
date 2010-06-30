package body Derived_Type is

   procedure Affect
     (Index_In : out Index_Int;
      Index_Re : out Index_Real)
   is
   begin
      Index_In := 5;
      Index_Re := 5.0;
   end Affect;

end Derived_Type;
