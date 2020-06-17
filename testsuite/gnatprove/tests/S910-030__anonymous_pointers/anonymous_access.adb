package body Anonymous_Access with SPARK_Mode is

   function Copy (X : List_Acc) return List_Acc is
      N : List_Acc;
   begin
      if X /= null then
         N := Copy (X.N);
         return new List'(V => X.V, N => N);
      end if;
      return null;
   end Copy;
end Anonymous_Access;
