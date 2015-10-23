package body Var is

   protected body PO is

      entry Dummy (for I in Variable_Range) when Standard.True is
      begin
         null;
      end Dummy;

   end PO;

end Var;
