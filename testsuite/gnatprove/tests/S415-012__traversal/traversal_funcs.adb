procedure Traversal_Funcs with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function Next (X : access List) return access List with Pre => True is
   begin
      if X /= null then
         return X.N;
      end if;
      return X;
   end Next;

   procedure P (X : access List) with Pre => True is
      C : access List := Next (X);
   begin
      if C /= null and then Next (C.N) /= null then
         C := Next (C.N).N;
      end if;
      if C /= null then
         C.V := 3;
      end if;
   end P;
begin
   null;
end Traversal_Funcs;
