package Prots is

   protected PO
     with Priority => 3
   is
      procedure Set_Value (B: Boolean)
      with Global => null, Always_Terminates;
      function Get_Value return Boolean
      with Side_Effects, Global => null, Always_Terminates;
      entry Wait_For_True (V : out Boolean)
      with Global => null, Always_Terminates;
   private
      Value : Boolean := False;
   end;

   procedure P1;
   --  Priority of the caller must be <= 3

   procedure P2;
   --  Priority of the caller must be <= 3

   procedure P3;
   --  Priority of the caller must be <= 3

end Prots;
