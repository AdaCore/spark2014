package body Aggregates
  with SPARK_Mode
is
   type Coordinate_T is record
      X : Integer;
      Y : Integer;
      Z : Integer;
   end record;

   --  We get some extra dependencies here

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

   --  We also get the extra dependencies when using aggregates

   procedure Test_02 (A, B, C : in     Integer;
                      D, E, F :    out Integer)
     with Global  => null,
          Depends => (D => A,
                      E => B,
                      F => C)
   is
      Tmp : Coordinate_T := Coordinate_T'(X => A,
                                          Y => B,
                                          Z => C);
   begin
      D := Tmp.X;
      E := Tmp.Y;
      F := Tmp.Z;
   end Test_02;

   --  others just works! :D

   procedure Test_03 (A, B, C : in     Integer;
                      D, E, F :    out Integer)
     with Global  => null,
          Depends => (D => A,
                      E => B,
                      F => C)
   is
      Tmp : Coordinate_T := Coordinate_T'(X      => A,
                                          Y      => B,
                                          others => C);
   begin
      D := Tmp.X;
      E := Tmp.Y;
      F := Tmp.Z;
   end Test_03;

   procedure Test_04 (A, B, C    : in     Integer;
                      D, E, F    :    out Integer)
     with Global  => null,
          Depends => (D => A,
                      E => B,
                      F => C)
   is
      Tmp : Coordinate_T := Coordinate_T'(X      => A,
                                          Y      => B,
                                          others => 0);
   begin
      D := Tmp.X;
      E := Tmp.Y;
      F := Tmp'Update (X => 0, Y => 0, Z => C).Z;
   end Test_04;
end Aggregates;
