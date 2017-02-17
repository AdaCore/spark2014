with Support; use Support;
procedure Client (H : out Boolean) is
   X, Y, Z : Boolean := True;
begin
   Verify (X);
   Verify (Y);
   Verify (Z);
   H := X and Y and Z;
end Client;

