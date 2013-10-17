package body Natural_Set is
   pragma SPARK_Mode (On);

   procedure Create (S : out T)
   is
   begin
      S := T'(Len => 0,
              M   => Set_Array_T'(others => Invalid_Element));
   end Create;

   procedure Insert (S     : in out T;
                     Value : in     Natural)
   is
      Old_Length : constant Integer := S.Len;
   begin
      if not Contains (S, Value) then
         S.Len       := S.Len + 1;
         S.M (S.Len) := Value;
      end if;
   end Insert;

end Natural_Set;
