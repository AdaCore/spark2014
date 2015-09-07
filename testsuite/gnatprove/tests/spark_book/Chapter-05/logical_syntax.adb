with Ada.Text_IO; use Ada.Text_IO;
procedure Logical_Syntax is
   A, B, C : Boolean := False;
   function Is_Prime (N : in Integer) return Boolean is
      -- stub for prime number determination
   begin
      if N > 1 then
         return True;
      else
         return False;
      end if;
   end Is_Prime;

   subtype Digit is Integer range -9 .. 9;

begin
   A := not B;
   A := B and C;
   A := B or C;
   A := B xor C;
   A := (if B then C else True);
   A := (if B then C);
   A := (for all X in Integer => (if X rem 10 = 0 then X rem 2 = 0));
   A := (for some X in Natural => (X rem 2 = 0 and then Is_Prime (X)));
   A := (for all X in Digit => X ** 2 < 100);
   if A then
      Put_Line ("Worked");
   end if;
   A := (for all X in Integer => (if X in Digit then X ** 2 < 100));

end Logical_Syntax;
