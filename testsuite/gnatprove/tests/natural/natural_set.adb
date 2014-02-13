package body Natural_Set
  with SPARK_Mode
is

   procedure Create (S : out T)
   is
   begin
      S := T'(Len => 0,
              M   => Set_Array_T'(others => Invalid_Element));
   end Create;

   procedure Insert (S     : in out T;
                     Value : in     Natural)
   is
   begin
      if not Contains (S, Value) then
         S.Len       := S.Len + 1;
         S.M (S.Len) := Value;
         pragma Assert (Contains (S, Value));
      end if;
   end Insert;

end Natural_Set;
