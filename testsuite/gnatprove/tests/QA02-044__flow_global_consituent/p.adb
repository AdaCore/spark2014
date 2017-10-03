package body P
  with Refined_State => (State => X),
       SPARK_Mode => Off
is
   function Proxy1 return Boolean is (X);
   function Proxy2 return Boolean is (X);
end;
