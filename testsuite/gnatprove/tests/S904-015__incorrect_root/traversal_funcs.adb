procedure Traversal_Funcs with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function F (X, Y : access constant List) return access constant List is
   begin
      return Y;
   end F;
begin
   null;
end Traversal_Funcs;
