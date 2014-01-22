package body RT
  with SPARK_Mode => On
is

   function F1 return Boolean is
      T1, T2 : Time;
   begin
      T1 := Clock;
      T2 := Clock;

      -- should NOT prove, since Clock accesses volatile state
      pragma Assert (T1 = T2);

      return T1 = T2;
   end F1;


end RT;
