package body Flow_Aggregate_Bug
  with SPARK_Mode
is
   type Coordinate_T is record
      X : Integer;
      Y : Integer;
      Z : Integer;
   end record;

   procedure Test (Input  : in     Integer;
                   Output :    out Integer)
     with Global  => null,
          Depends => (Output => Input)
   is
   begin
      Output := Coordinate_T'(X => 0, Y => 0, Z => Input).Z;
   end Test;
end Flow_Aggregate_Bug;
