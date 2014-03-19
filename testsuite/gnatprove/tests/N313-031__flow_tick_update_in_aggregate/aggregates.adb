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

   procedure Test (Input  : in out Coordinate_T;
                   Output :    out Double_Coordinate_T)
     with Global  => null,
          Depends => ((Input,
                       Output) => Input)
   is
   begin
      Output := (C1 => Input'Update (X => 0),
                 C2 => (X => Input.X, Y => 0, Z => 0));

      Input  := (X => Output.C2.X,
                 Y => Output.C2'Update (Y => Input.X).X,
                 Z => 0);
   end Test;
end Aggregates;
