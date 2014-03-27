package body Types is
   type Volatile_Integer is new Integer with Volatile;

   procedure Test_01 (I : in     Volatile_Integer;
                      O :    out Volatile_Integer)
   is
   begin
      O := I;
      O := I;
   end Test_01;
end Types;
