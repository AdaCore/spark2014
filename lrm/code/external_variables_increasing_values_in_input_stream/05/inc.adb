package body Inc
--# own Sensor is in S;
is
   S : Integer;
   for S'Address use 16#DEADBEEF#;
   pragma Volatile (S);

   procedure Read (V     : out Integer;
                   Valid : out Boolean)
   --# global in S;
   --# post (Valid -> V = S~) and
   --#      (S = S'Tail (S~));
   is
      Tmp : Integer;
   begin
      Tmp := S;
      if Tmp'Valid then
         V := Tmp;
         Valid := True;
         --# check S = S'Tail (S~);
      else
         V := 0;
         Valid := False;
      end if;
   end Read;

   procedure Increases (Result : out Boolean;
                        Valid  : out Boolean)
   --# global in S;
   --# post Valid -> (Result <-> S'Tail (S~) > S~);
   is
      A, B : Integer;
   begin
      Result := False;
      Read (A, Valid);
      if Valid then
         Read (B, Valid);
         if Valid then
            Result := B > A;
         end if;
      end if;
   end Increases;

end Inc;
