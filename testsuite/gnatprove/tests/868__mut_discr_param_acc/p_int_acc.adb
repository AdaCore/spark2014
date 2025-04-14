package body P_Int_Acc is

   procedure Proc1 (Rec : not null access T; B : Boolean) is
   begin
      if B then
         pragma Assert (not Rec.all'Constrained);  --  @ASSERT:FAIL

      else
         Rec.all := T'(K => 999);  --  @DISCRIMINANT_CHECK:FAIL
      end if;
   end Proc1;

   procedure Proc2 (Rec : not null access constant T; B : Boolean) is
   begin
      if B then
         pragma Assert (not Rec.all'Constrained);  --  @ASSERT:FAIL

      else
         null;  -- Cannot assign via a constant access
      end if;

   end Proc2;

   procedure Proc3 (Rec : not null T_Acc; B : Boolean) is
   begin
      if B then
         pragma Assert (not Rec.all'Constrained);  --  @ASSERT:FAIL

      else
         Rec.all := T'(K => 999);  --  @DISCRIMINANT_CHECK:FAIL
      end if;
   end Proc3;

end P_Int_Acc;
