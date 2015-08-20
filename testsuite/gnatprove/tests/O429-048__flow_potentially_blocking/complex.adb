with Ada.Numerics.Complex_Types;
with Ada.Text_IO.Complex_IO;

procedure Complex is
   X : Ada.Numerics.Complex_Types.Complex;

   package CIO is new Ada.Text_IO.Complex_IO (Ada.Numerics.Complex_Types);

begin
   X.Re := 0.0;
   X.Im := 0.0;
   CIO.Put (X);
end;
