package body Attributes
is

   procedure Test_Min (X, Y, Z : in Integer;
                       W       : out Integer)
   with Global => null,
        Depends => (W => (X, Y, Z))
   is
   begin
      W := Integer'Max (Integer'Min (X, Y), Z);
   end Test_Min;

   procedure Test_Mod (X : in Integer;
                       W : out Integer)
   is
      type T is mod 256;
   begin
      W := Integer (T'Mod (T (X)));
   end Test_Mod;

end Attributes;
