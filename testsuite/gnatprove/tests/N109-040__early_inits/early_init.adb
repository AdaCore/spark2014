package body Early_Init
is

   package body Inner_1
   is
      function F1 (X : Positive) return Positive is (X);
   begin
      V1 := 88;
   end Inner_1;

   package body Inner_2
   is
      function F2 (Y : Positive) return Positive is (Y);
   end Inner_2;

   package Inner_3
   with Initializes => V3
   is
      V3 : Positive;
   end Inner_3;
       package Inner_4
   with Initializes => (V4 => Inner_3.V3)
   is
      V4 : Positive := Inner_3.V3;
   end Inner_4;

   package body Inner_3 is
   begin
      V3 := 88;
   end Inner_3;

end Early_Init;
