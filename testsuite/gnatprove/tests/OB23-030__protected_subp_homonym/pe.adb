package body PE is

   protected body PT is
      entry Set (Q : Integer) when True is
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
