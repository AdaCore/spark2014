package body Bad_Refinement
  with Refined_State => (State  => X,
                         State2 => (Y, Z))
is
   X, Y, Z : Integer := 0;

   procedure Liar (I : out Integer) is
   begin
      I := Y;
   end Liar;

   procedure Liar2 (I : out Integer) is
   begin
      I := X + Y;
   end Liar2;

   procedure Liar3 (I : out Integer) is
   begin
      I := 10;
      X := 5;
   end Liar3;

   function Liar4 return Integer is
   begin
      return Y;
   end Liar4;

   procedure Liar5 (I : out integer) is
   begin
      I := X;
      Y := X + Y;
   end Liar5;

    procedure Liar6 (I, J : out Integer) is
    begin
       I := 0;
       J := X;
    end Liar6;

    procedure Liar7 (I, J : out Integer) is
    begin
       I := 0;
       J := X;
    end Liar7;

   procedure Liar8
     with Refined_Depends => (X => Y)
   is
   begin
      X := Z;
   end Liar8;

   procedure Liar9 (I : out Integer) is
   begin
      I := Z;

      X := 0;
   end Liar9;
end Bad_Refinement;
