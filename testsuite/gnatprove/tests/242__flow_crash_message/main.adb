procedure Main with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      D : Integer;
      N : List_Acc;
   end record;

   procedure Contains (L : not null access List) is
   begin
      null;
   end Contains;
begin
   null;
end Main;
