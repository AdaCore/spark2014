package P is

   protected PO is
      function F return Boolean;
   end;

   X : Integer := 0 with Volatile, Part_Of => PO;

end;
