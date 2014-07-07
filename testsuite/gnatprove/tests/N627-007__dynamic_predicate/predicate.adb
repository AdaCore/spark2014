package body Predicate with SPARK_Mode is

   procedure Call (Value : Str) is
   begin
      for J in Value'Range loop
         pragma Assert (Value(J) in 'a' .. 'b');
      end loop;
   end Call;

end Predicate;
