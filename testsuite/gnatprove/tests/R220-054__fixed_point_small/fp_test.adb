package body FP_Test is
   pragma SPARK_Mode (On);
   function Add_Signals (A : in Signal_Type; B : in Signal_Type) return
     Signal_Type is
   begin
      return (A + B);
   end Add_Signals;
end FP_Test;
