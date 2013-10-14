procedure Dynamic_In_Post is
   procedure Test_1 is
      function Get_Last (S : String) return Integer is (S(S'First .. S'Last)'Last);
      X : String := "hello";
      Y : String := "you";
   begin
      pragma Assert (Get_Last (X) = Get_Last (Y));
   end Test_1;

   procedure Test_2 is
      function Get_Last (S : String) return Integer
        with Post => Get_Last'Result = S(S'First .. S'Last)'Last
      is
      begin
         return S'Last;
      end Get_Last;
      X : String := "hello";
      Y : String := "you";
      A : Integer := Get_Last (X);
      B : Integer := Get_Last (Y);
   begin
      pragma Assert (A = B);
   end Test_2;

   procedure Test_3 is
      S : String := "hello";
      X : Positive := 1;
   begin
      while S(S'First .. X)'Last = X loop
         pragma Assert (X = 1);
         X := 2;
      end loop;
   end Test_3;
begin
   Test_1;
   Test_2;
   Test_3;
end Dynamic_In_Post;
