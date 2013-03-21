package body Message_Tests
is
   type Flags_T is record
     A, B : Boolean;
   end record;

   type Coordinate is record
      X     : Float;
      Y     : Float;
      W     : Float;
      Flags : Flags_T;
   end record;

   procedure Not_All_Used_In_1 (C : Coordinate;
                                W : out Float)
   is
   begin
      --  It may make more sense to have only a float as the in
      --  argument.
      W := C.W;
   end Not_All_Used_In_1;

   procedure Not_All_Used_In_2 (C : Coordinate;
                                B : out Boolean)
   is
   begin
      --  It may make more sense to have only a Flags_T as the in
      --  argument.
      B := C.Flags.A and C.Flags.B;
   end Not_All_Used_In_2;

   procedure Not_All_Used_In_3 (C : Coordinate;
                                W : out Float)
   is
   begin
      --  This is OK and should not raise an error.
      W := C.X + C.Y;
   end Not_All_Used_In_3;

   procedure Not_All_Used_In_4 (C : Coordinate;
                                W : out Float)
   is
   begin
      --  Unused C.
      W := 1.0;
   end Not_All_Used_In_4;

   procedure Not_All_Used_Out (C : out Coordinate)
   is
   begin
      C.X := 0.0;
      C.Y := 0.0;
      --  C.W is not defined. Definitely an error.
   end Not_All_Used_Out;

   procedure Undefined_Used_1 (C : out Coordinate)
   is
      F : Flags_T;
   begin
      F.A := False;
      --  We have not set F.B

      C.X := 0.0;
      C.Y := 0.0;
      C.W := 1.0;
      C.Flags := F;
   end Undefined_Used_1;

end Message_Tests;
