package body Pack is

   procedure Q is

      function F return Integer is (0)
      with Pre => True;

      X : Integer := F;
   begin
      pragma Assert (X = 0);
      X := X + 1;
      pragma Assert (X = 1);
      X := X + 2;
      pragma Assert (X = 3);
   end Q;

   procedure P is separate;
end Pack;
