with Ada.Text_IO;          use Ada.Text_IO;
with Ada.Integer_Text_IO;  use Ada.Integer_Text_IO;
with Ada.Float_Text_IO;    use Ada.Float_Text_IO;
procedure Average is  -- Shorter version with "use clauses"
   -- Display the average of two integers entered by the user
   A : Integer;   -- The first integer
   B : Integer;   -- The second integer
   M : Float;     -- The average of the two integers
begin
   Put_Line ("Enter two integers.");
   Get (A);
   Get (B);
   New_Line;

   M := Float (A + B) / 2.0;

   Put ("The Average of your two numbers is ");
   Put (M, 1, 2, 0);
   New_Line;
end Average;
