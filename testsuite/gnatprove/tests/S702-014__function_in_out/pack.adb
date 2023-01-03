package body Pack
  with SPARK_Mode, Refined_State => (State => null)
is
   function Has return Boolean with
     SPARK_Mode => Off
   is
   begin
      return True;
   end Has;

end Pack;
