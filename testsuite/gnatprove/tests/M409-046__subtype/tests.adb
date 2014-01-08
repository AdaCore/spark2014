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

   procedure Mem_Vowels (V : in out Vowels; X : My_Enum) is
   begin
      if X in Vowels then
         V := X;
      end if;
   end Mem_Vowels;

   procedure Mem_Positive_But_Not_Ten (V : in out Positive_But_Not_Ten; X : Positive) is
   begin
      if X in Positive_But_Not_Ten then
         V := X;
      end if;
   end Mem_Positive_But_Not_Ten;

   procedure Mem_Positive_With_Hole (V : in out Positive_With_Hole; X : Positive) is
   begin
      if X in Positive_With_Hole then
         V := X;
      end if;
   end Mem_Positive_With_Hole;

   procedure Mem_Positive_Not_One (V : in out Positive_Not_One; X : Positive) is
   begin
      if X in Positive_Not_One then
         V := X;
      end if;
   end Mem_Positive_Not_One;

end Tests;
