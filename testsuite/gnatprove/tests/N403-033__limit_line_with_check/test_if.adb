package body Test_If is

   function Test (A : integer) return Integer is
      B : Integer;
      C : integer := 3;
   begin
      if (a = 0) then
         B := 500;
      else
         B := 1000;
      end if;

      C := C + B;

      while B < Integer'Last / 2 loop
         pragma Loop_Invariant (B < Integer'Last / 2);
         B := 1 + B;
      end loop;

      C := C + B;

      return C;
   end;

end Test_If;
