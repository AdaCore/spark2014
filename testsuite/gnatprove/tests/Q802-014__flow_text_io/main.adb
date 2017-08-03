with Ada.Text_IO;

procedure Main is

   package P is new Ada.Text_IO.Integer_IO (Integer);

   use P;

begin

   Put (10);

end Main;
