package One is

   subtype Single_Range is Integer range 1 .. 1;

   protected PO is
      entry Dummy (Single_Range);
   end;

end;
