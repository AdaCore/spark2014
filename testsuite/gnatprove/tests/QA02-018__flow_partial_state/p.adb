package body P
  with Refined_State => (State => (X, Y)),
       SPARK_Mode => Off
is
   Y : Boolean := True;

   function Proxy return Boolean is (X and Y);
end;
