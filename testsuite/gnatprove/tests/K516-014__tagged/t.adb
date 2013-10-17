package body T is pragma SPARK_Mode (Off);
   function Get return T1 is
   begin
      return T1'(X => 0);
   end;
end;
