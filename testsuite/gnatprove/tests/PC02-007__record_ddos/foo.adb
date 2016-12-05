package body Foo is

   type Level_1 is record
      B : Boolean;
      F : Float;
      I : Integer;
   end record;

   type Level_2 is record
      R1, R2, R3, R4, R5 : Level_1;
   end record;

   type Level_3 is record
      R1, R2, R3, R4, R5 : Level_2;
   end record;

   type Level_4 is record
      R1, R2, R3, R4, R5 : Level_3;
   end record;

   type Level_5 is record
      R1, R2, R3, R4, R5 : Level_4;
   end record;

   type Level_6 is record
      R1, R2, R3, R4, R5 : Level_5;
   end record;

   procedure Fiddle (R : in out Level_6)
   is
   begin
      R := (others =>
              (others =>
                 (others =>
                    (others =>
                       (others =>
                          (False, 0.0, 0))))));
      pragma Assert (R.R1.R1.R1.R1.R1.B xor R.R1.R1.R1.R1.R1.B
                       = R.R1.R1.R1.R1.R1.B);
   end Fiddle;

end Foo;
