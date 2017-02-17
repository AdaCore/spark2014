package body Test is

   procedure Swap (S : in out T; I1, I2 : Entry_Id)
      with Post => Get_Remaining (S) = Get_Remaining (S'Old);

   procedure Swap (S : in out T; I1, I2 : Entry_Id) is
      Tmp : Integer := S.Cards (I1);
   begin
      S.Cards (I1) := S.Cards (I2);
      S.Cards (I2) := Tmp;
   end Swap;

   procedure Next (S : in out T) is
   begin
      S.Index := S.Index + 1;
      Swap (S, S.Index, S.Index + Entry_Id (S.Remaining rem Entry_Id'Modulus));
   end Next;

   procedure P (S : in out T) is
   begin
      S.Remaining := S.Remaining - 1;
      Next (S);
   end P;

end Test;
