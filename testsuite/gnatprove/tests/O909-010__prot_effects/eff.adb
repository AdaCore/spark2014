package body Eff is

   Bar : Boolean := True;

   protected body Ty is

      function Get_A return Integer is (A);
      function Get_B return Integer is (B);

      procedure Set_B_To_Sum_Plus (Add : Integer) is
      begin
         B := B + A + Add;
      end Set_B_To_Sum_Plus;

      entry Set_B_To_Sum_Plus_E (Add : Integer) when True is
      begin
         pragma Assert (Get_A = 10); --@ASSERT:FAIL
         B := B + A + Add;
      end Set_B_To_Sum_Plus_E;
   end Ty;

   procedure P is begin
      pragma Assert (Shared.Get_A = 10);
      Shared.Set_B_To_Sum_Plus(10);
   end P;

   procedure Q is begin
      Shared.Set_B_To_Sum_Plus_E(10);
   end Q;
end Eff;
