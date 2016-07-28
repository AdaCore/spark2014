package body User_Lemma is

   procedure Number_Is_Prime (N : Positive) is
   begin
      pragma Assume (Is_Prime (N));
   end Number_Is_Prime;

   procedure Test is
   begin
      Number_Is_Prime (15486209);
      pragma Assert (Is_Prime (15486209));

      pragma Assert (Is_Prime (15487001));
      pragma Assert (Is_Prime (15487469));

      Number_Is_Prime (10);
      pragma Assert (Is_Prime (10));
   end Test;

end User_Lemma;
