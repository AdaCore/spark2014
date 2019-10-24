package body Test
with
   Refined_State => (State => (Count, Root_Idx))
is

   Root_Idx : Index_Type := 0;

   function Root return Index_Type is (Root_Idx);

   procedure Clear (I : Index_Type)
   is
   begin
      Count (I) := 0;
   end Clear;

end Test;
