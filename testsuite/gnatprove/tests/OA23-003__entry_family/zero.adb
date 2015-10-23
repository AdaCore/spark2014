package body Zero is

   protected body PO is

      entry Dummy (for I in Null_Range) when Standard.True is
      begin
         null;
      end Dummy;

   end PO;

end Zero;
