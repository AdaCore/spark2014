package body Test with SPARK_Mode is

   procedure Do_Smth (I : Boolean; Oha : out T) is
   begin
      Oha := (if I then 0 else 16); --@RANGE_CHECK:FAIL
   end Do_Smth;

end Test;
