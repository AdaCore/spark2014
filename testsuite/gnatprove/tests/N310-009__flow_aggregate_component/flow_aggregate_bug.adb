package body Flow_Aggregate_Bug
is
   type Vec3 is record
      X : Integer;
      Y : Integer;
      Z : Integer;
   end record;

   type Opt is record
      Exists : Boolean;
      V      : Vec3;
   end record;

   procedure Test (Input  : in     Integer;
                   Output :    out Integer)
     with Global  => null,
          Depends => (Output => Input)
   is
   begin
      Output := Opt'(Exists => True,
                     V      => (X => 0,
                                Y => 0,
                                Z => Input)).V.Z;
   end Test;

end Flow_Aggregate_Bug;
