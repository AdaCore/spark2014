package Iomsg
  with SPARK_Mode => On
is
   function Do_Something return Boolean with
     Post => Do_Something'Result = True;
private
   pragma SPARK_Mode (Off);
   type T is new Boolean;
   Stuff : T;
end;
