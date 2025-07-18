package body P_Int is

   procedure Proc1 (Rec : in out T) is
   begin
      Rec := T'(K => 999);   --  @DISCRIMINANT_CHECK:FAIL
   end Proc1;

   procedure Proc2 (Rec : out T) is
   begin
      Rec := T'(K => 999);   --  @DISCRIMINANT_CHECK:FAIL
   end Proc2;

end P_Int;
