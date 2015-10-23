package Var is

   X : Integer;

   subtype Variable_Range is Integer range 1 .. X;

   protected PO is
      entry Dummy (Variable_Range);
   end;

end;
