pragma Extensions_Allowed (All_Extensions);

procedure Test with SPARK_Mode is
   type Matrix is array (1 .. 2, 1 .. 2) of Integer;

   type Rec is record
      Value : Integer;
   end record;

   type Rec_Array is array (1 .. 2) of Rec;

   type Fixed_Array is array (1 .. 2) of Integer;
   type Wrapper is record
      A : Fixed_Array;
   end record;

   M : Matrix := (others => (others => 0));
   R : Rec_Array := (others => (Value => 0));
   W : Wrapper := (A => (0, 0));
begin
   <<Capture>>
   null;
   pragma Assert (M'At (Capture) = M);
   pragma Assert (R'At (Capture) = R);
   pragma Assert (W.A'At (Capture) = W.A);
end Test;
