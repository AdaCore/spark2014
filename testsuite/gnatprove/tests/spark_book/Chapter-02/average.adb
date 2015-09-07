with Ada.Text_IO;
with Ada.Integer_Text_IO;
with Ada.Float_Text_IO;
procedure Average is
   -- Display the average of two integers entered by the user
   A : Integer;   -- The first integer
   B : Integer;   -- The second integer
   M : Float;     -- The average of the two integers
begin
   Ada.Text_IO.Put_Line (Item => "Enter two integers.");
   Ada.Integer_Text_IO.Get (Item => A);
   Ada.Integer_Text_IO.Get (Item => B);
   Ada.Text_IO.New_Line;

   M := Float (A + B) / 2.0;

   Ada.Text_IO.Put (Item => "The Average of your two numbers is ");
   Ada.Float_Text_IO.Put (Item => M,
                          Fore => 1,
                          Aft  => 2,
                          Exp  => 0);
   Ada.Text_IO.New_Line;
end Average;
