package body Anonymous_Access with SPARK_Mode is

   function Copy (X : List_Acc) return List_Acc is
   begin
      if X /= null then
         declare
            N : List_Acc := Copy (X.N);
         begin
            return new List'(V => X.V, N => N);
         end;
      end if;
      return null;
   end Copy;
end Anonymous_Access;
