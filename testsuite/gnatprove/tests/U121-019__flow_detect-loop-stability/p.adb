procedure P
   with SPARK_Mode => On
is
   I : Natural := 0;

   procedure Useless (X : in out Integer)
   is
   begin
      X := X;
   end Useless;

   procedure Infinite_Loop
      with Global => (In_Out => I)
   is
   begin
      while I < 10 loop

         -- We want to be able to detect that I is 'stable' in the loop, i.e.
         -- it does not change over iterations, and so this is an infinite
         -- loop. Currently this detection is not supported.

         Useless (I);

      end loop;
   end Infinite_Loop;

begin
   Infinite_Loop;
end P;
