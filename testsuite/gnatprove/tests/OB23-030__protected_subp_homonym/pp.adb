package body PP is

   protected body PT is
      procedure Set (Q : Integer) is
      begin
         P_Int := Q;
      end;

      procedure Set (Q : Boolean) is
      begin
         P_Bool := Q;
      end;

   end PT;

   procedure Proc is
   begin
      PO.Set (0);
      PO.Set (True);
   end Proc;

end;
