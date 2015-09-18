package Eff is

   protected Type Ty is

      function Get_A return Integer;
      function Get_B return Integer;
      procedure Set_B_To_Sum_Plus (Add : Integer)
         with Pre => Add > 0;
      entry Set_B_To_Sum_Plus_E (Add : Integer)
         with Pre => Get_A = 10;
   private
      A : Integer := 0;
      B : Integer := 1;
   end Ty;

   Shared : Ty;

   procedure P
      with Pre => Shared.Get_A = 10;
   procedure Q;

end Eff;
