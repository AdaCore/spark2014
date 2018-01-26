with Longest_Common_Prefix; use Longest_Common_Prefix;

procedure Main
  with SPARK_Mode => On
is
   pragma Warnings (Off);
   A : Boolean;
begin
--     Longest_Common_Prefix.A := (1, 2, 3, 4, 5, 1, 2, 3, 4, 5, others => 0);
--     A := Longest_Common_Prefix.LCP ( 1, 6) = 5;
--     A := Longest_Common_Prefix.LCP (1, 1001) = 0;
--     A := Longest_Common_Prefix.LCP ( 1, 7) = 0;

   Longest_Common_Prefix.A := (1, 2, 3, 4, 5, 1, 2, 3, 4, 5, others => 0);

   pragma Assert (Longest_Common_Prefix.A (1 .. 5) = Longest_Common_Prefix.A (6 .. 10));

   pragma Assert (Longest_Common_Prefix.LCP (1, 6) = 5);

   pragma Assert (Longest_Common_Prefix.LCP (1, 7) = 0);

   pragma Assert (Longest_Common_Prefix.LCP (1, 1001) = 0);  -- should fail
end Main;
