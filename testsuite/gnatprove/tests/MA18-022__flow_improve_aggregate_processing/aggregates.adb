package body Aggregates
  with SPARK_Mode
is
   type Coordinate_T is record
      X : Integer;
      Y : Integer;
      Z : Integer;
   end record;

   type Double_Coordinate_T is record
      C1 : Coordinate_T;
      C2 : Coordinate_T;
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

   procedure Test_04 (A, B, C : in     Integer;
                      D, E, F :    out Integer)
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

   procedure Test_05 (Input  : in     Integer;
                      Output : in out Coordinate_T)
     with Global  => null,
          Depends => (Output =>+ Input)
   is
   begin
      Output := Output'Update (X => Output.X, Y => Output.Y, Z => Input);
   end Test_05;

   procedure Test_06 (Input  : in     Double_Coordinate_T;
                      Output :    out Coordinate_T)
     with Global  => null,
          Depends => (Output => Input)
   is
      Tmp : Coordinate_T := Coordinate_T'(X      => 0,
                                          Y      => 0,
                                          others => 0);
   begin
      Output := Input'Update (C1 => Tmp).C2;
   end Test_06;

   procedure Test_07 (Input  : in     Coordinate_T;
                      Output :    out Double_Coordinate_T)
     with Global  => null,
          Depends => (Output => Input)
   is
   begin
      Output.C1 := Input'Update (X => 0,
                                 Y => 0,
                                 Z => 0);

      Output.C2 := Input'Update (X => Input.X,
                                 Y => Input.Y,
                                 Z => Input.Z);
   end Test_07;

   procedure Test_08 (Input  : in     Coordinate_T;
                      Output :    out Double_Coordinate_T)
     with Global  => null,
          Depends => (Output => Input)
   is
   begin
      Output := (Input, C2 => (X => 0, Y => 0, Z => 0));
   end Test_08;
end Aggregates;
