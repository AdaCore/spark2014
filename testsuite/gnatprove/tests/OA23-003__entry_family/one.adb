package body One is

   protected body PO is

      entry Dummy (for I in Single_Range) when Standard.True is
      begin
         null;
      end Dummy;

   end PO;

end One;
