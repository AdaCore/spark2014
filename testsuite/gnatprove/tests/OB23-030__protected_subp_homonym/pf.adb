package body PF is

   protected body PT is
      function Get return Integer is
      begin
         return P_Int;
      end;

      function Get return Boolean is
      begin
         return P_Bool;
      end;

   end PT;

   procedure Proc is
      X : constant Integer := PO.Get;
      Y : constant Boolean := PO.Get;
   begin
      null;
   end Proc;

end;
