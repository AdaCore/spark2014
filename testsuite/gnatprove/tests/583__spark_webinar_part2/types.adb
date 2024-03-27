package body Types
  with SPARK_Mode
is

   procedure Assign
     (A : in out Table;
      I : Index;
      P : Element)
   is
   begin
      A (I) := P;
   end Assign;

end Types;
