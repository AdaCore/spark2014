with Interfaces;
package body P
  with SPARK_Mode => On
is
   package Inner is
      procedure Wibble (S : in Integer; R : out Integer)
	with Depends => (R => S);
   end Inner;

   package body Inner is separate;

   procedure Op1 (X, Y : in Integer; Z : out Integer) is
      L : Interfaces.Unsigned_32;
   begin
      L := Interfaces.Shift_Right (Interfaces.Unsigned_32 (X + Y), 5); -- Warning here kills all further analysis?
      Inner.Wibble (Integer (L), Z); -- expect flow error
   end Op1;

   procedure Op2 (X, Y : in Integer; Z : out Integer) is
      L : Interfaces.Unsigned_32;
   begin
      L := Interfaces.Unsigned_32 (X + Y);
      Inner.Wibble (Integer (L), Z); -- expect flow error
   end Op2;

end P;
