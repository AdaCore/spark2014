package body Test is

   function Random_Number return Integer is
      N : Integer := 4; --  Chosen by fair dice roll
   begin
      return N;
   end Random_Number;

   function Multiple_Returns (A : in Boolean) return Integer is
   begin
      if A then
         return 42;
      else
         return 9;
      end if;
   end Multiple_Returns;

   function Is_Prime (N : in Positive) return Boolean is
   begin
      for I in Positive range 2 .. N / 2 loop
         if N mod I = 0 then
            return False;
         end if;
      end loop;
      return True;
   end Is_Prime;

   function Ext_Return_01 (N : in Positive) return Integer is
   begin
      return R : Integer do
         R := N + 1;
      end return;
   end Ext_Return_01;

   function No_Return (N : in Integer) return Boolean is
   begin
      if N > 0 then
         return True;
      end if;
      if N < 0 then
         return False;
      end if;

      raise Program_Error;
   end No_Return;

end Test;
