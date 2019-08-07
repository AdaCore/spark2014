package P is
   protected type PT is
      procedure Proc;
   end PT;

   type A is array (Boolean) of PT;
end;
