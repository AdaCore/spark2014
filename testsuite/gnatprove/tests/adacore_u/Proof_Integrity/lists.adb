package body Lists with SPARK_Mode is
   function Goes_To (I, J : Index) return Boolean is
   begin
      if Memory1 (I).Is_Set then
         return Memory1 (I).Next = J;
      else
         return False;
      end if;
   end Goes_To;

   procedure Link (I, J : Index) is
   begin
      Memory1 (I) := (Is_Set => True, Next => J);
   end Link;
end Lists;
