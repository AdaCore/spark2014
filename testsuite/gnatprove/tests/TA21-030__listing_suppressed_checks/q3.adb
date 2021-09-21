procedure Q3 is --  No explicit SPARK_Mode !
   function No_Way (A : Integer) return Integer is (A - Integer'Last)
     with SPARK_Mode => Off;
   Bar : Integer;
begin
    Bar := No_Way (1);
end Q3;
