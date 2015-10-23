package Zero is

   subtype Null_Range is Integer range 1 .. 0;

   protected PO is
      entry Dummy (Null_Range);
   end;

end;
