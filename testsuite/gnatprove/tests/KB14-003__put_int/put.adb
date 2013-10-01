with Ada.Text_IO; use Ada.Text_IO;
procedure Put (X : Integer) is

   Int   : Integer;
   S     : String (1 .. Integer'Width);
   First : Natural := S'Last + 1;
   Val   : Integer;

begin
   --  Work on negative values to avoid overflows
   Int := (if X < 0 then X else -X);

   loop
      --  Cf RM 4.5.5 Multiplying Operators.  The rem operator will return
      --  negative values for negative values of Int.
      Val := Int rem 10;
      Int := (Int - Val) / 10;
      First := First - 1;
      S (First) := Character'Val (Character'Pos ('0') - Val);
      exit when Int = 0;
   end loop;

   if X < 0 then
      First := First - 1;
      S (First) := '-';
   end if;

   Put (S (First .. S'Last));
end Put;
