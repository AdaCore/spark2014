package body Tests is

   procedure Enum (V : in out Vowels) is
   begin
      pragma Assert (V /= B);
      V := B;
   end Enum;

   procedure Pos_Not_Ten (V : in out Positive_But_Not_Ten) is
   begin
      pragma Assert (V /= 10);
      V := 10;
   end Pos_Not_Ten;

   procedure Pos_Hole (V : in out Positive_With_Hole) is
   begin
      pragma Assert (V /= 15);
      V := 10;
   end Pos_Hole;

   procedure Pos_Not_One (V : in out Positive_Not_One) is
   begin
      pragma Assert (V /= 1);
      V := 1;
   end Pos_Not_One;
end Tests;
