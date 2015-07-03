with Ada.Text_IO;
with Ada.Float_Text_IO;

with Support; use Support;

procedure Test is
   F : constant Float := Float (Prot.Get) / Float (Number_Of_Tasks);
begin
   --  Print the average number
   Ada.Text_IO.Put ("Average number is: ");
   Ada.Float_Text_IO.Put (F);
end Test;
