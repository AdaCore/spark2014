package body Prots is

   protected body PO is
      procedure Set_Value (B: Boolean) is
      begin
         Value := B;
      end;

      function Get_Value return Boolean is
         B: Boolean := Value;
      begin
         return Value;
      end;

      entry Wait_For_True (V : out Boolean) when Value is
      begin
         V := Value;
      end;
   end;

   procedure P1 is
   begin
      PO.Set_Value (True);
   end;

   procedure P2 is
      X : Boolean;
   begin
      X := PO.Get_Value;
   end;

   procedure P3 is
      X : Boolean;
   begin
      PO.Wait_For_True (X);
   end;

end Prots;
