procedure Main
with SPARK_Mode => On
is
   type My_Index is mod 4;
   type My_String is array (My_Index range <>) of Character;

   S1 : My_String (0 .. 3) := "toto";
   S2 : My_String := "t";

begin
   pragma Assert (S1 > "tata");
   pragma Assert (S1 > "tot");
   pragma Assert (S1 > (1 .. 0 => 'a'));
   pragma Assert (not (S1 > S1));
   pragma Assert ((1 .. 0 => 'a') < S1);
   pragma Assert ((1 .. 0 => 'a') < S2);
   pragma Assert (S2 > (1 .. 0 => 'a'));
   pragma Assert (S2 < "t"); --@ASSERT:FAIL
end Main;
