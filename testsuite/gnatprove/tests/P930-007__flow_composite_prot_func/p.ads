package P is

   protected type PT is
      function F return Boolean;
   end PT;

   type PR is record
      C : PT;
   end record with Volatile;

   type PA is array (Boolean) of PT;

   PO1 : PR;
   PO2 : PA;

end;
