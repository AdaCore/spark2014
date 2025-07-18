package body P_Bool is

   procedure Proc1 (Rec : in out T) is
   begin
      Rec := T'(K1 => True);   --  @DISCRIMINANT_CHECK:FAIL
   end Proc1;

   procedure Proc2 (Rec : out T) is
   begin
      Rec := T'(K1 => True);   --  @DISCRIMINANT_CHECK:FAIL
   end Proc2;

end P_Bool;
