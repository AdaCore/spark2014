package P is

   protected type PT is
      procedure Set (Q : Integer);
      procedure Set (Q : Boolean);
   private
      P_Int : Integer;
      P_Bool: Boolean;
   end;

   PO : PT;

   procedure Proc;

end;
