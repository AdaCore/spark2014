package body P is

   protected body PT is
      entry E when True is
      begin
         null;
      end;

      procedure Proc is null;

      function Func return Boolean is (True);
   end;

   procedure Flip (PO : in out PT) is
      Dummy : constant Boolean := PO.Func;
   begin
      PO.E;
      PO.Proc;
   end;

   function Flip (PO : PT) return Boolean is
      Dummy : constant Boolean := PO.Func;
   begin
      return Dummy;
   end;

end;
