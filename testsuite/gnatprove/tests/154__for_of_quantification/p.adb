procedure P (I : Integer)
  with SPARK_Mode
is
   X : String := "h";
begin
   case I is
      when 0 =>
         pragma Assert (for all C of X => C = 'x');
      when 1 =>
         pragma Assert (for some C of X => C = 'x');
      when others =>
         for C of X loop
            pragma Assert (C = 'x');
         end loop;
   end case;
end P;
