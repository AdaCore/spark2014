procedure Test with SPARK_Mode => On is
   procedure T;
   procedure T with SPARK_Mode => Off is
      procedure P;

      procedure P is null with SPARK_Mode => On;
   begin
      null;
   end T;
begin
   null;
end Test;
