package body Update_Legal_3
  with SPARK_Mode
is
   type Coordinate_T is record
      X : Integer;
      Y : Integer;
      Z : Integer;
   end record;

   procedure Test_01 (A, B, C : in     Integer;
                      D, E, F :    out Integer)
     with Global  => null,
          Depends => (D => A,
                      E => B,
                      F => C)
   is
      Tmp : Coordinate_T := (A, A, A);
   begin
      Tmp := Tmp'Update (Y => B,
                         Z => C);
      D := Tmp.X;
      E := Tmp.Y;
      F := Tmp.Z;
   end Test_01;
end Update_Legal_3;
