package PF is

   protected type PT is
      function Get return Integer;
      function Get return Boolean;
   private
      P_Int : Integer := 0;
      P_Bool: Boolean := False;
   end;

   PO : PT;

   procedure Proc;

end;
