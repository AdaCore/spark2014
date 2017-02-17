package T
is
   type Input_T is mod 2 ** 16;

   S_Max   : constant := 10.0;
   S_MSB   : constant := S_Max * 2.0;
   S_Scale : constant := 2.0 ** 16 / S_MSB;

   type Scale_T is digits 6 range 0.25 .. 1.0;

   type Output_T is digits 6 range -32.0 .. 32.0;

end T;

