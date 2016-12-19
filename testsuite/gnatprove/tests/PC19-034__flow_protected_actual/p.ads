package P is

   protected type PT is
      entry E;
      procedure Proc;
      function Func return Boolean;
   end;

   PO1, PO2 : PT;

   procedure Flip (PO : in out PT);
   function Flip (PO : PT) return Boolean with Volatile_Function;

end;
