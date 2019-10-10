procedure Traversal_Funcs with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function Next (X : access constant List) return access constant List with Pre => True is
   begin
      if X /= null then
         return X.N;
      end if;
      return null;
   end Next;
begin
   null;
end Traversal_Funcs;
