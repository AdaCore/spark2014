package PE is

   protected type PT is
      entry Set (Q : Integer);
      procedure Set (Q : Boolean);
   private
      P_Int : Integer := 0;
      P_Bool: Boolean := False;
   end;

   PO : PT;

   procedure Proc;

end;
