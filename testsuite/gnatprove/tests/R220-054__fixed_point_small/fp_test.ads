package FP_Test is
   pragma SPARK_Mode (On);

   Sample_Rate_Hz : constant := 500;
   Signal_Denominator : constant := 400;

   type Signal_Type is delta 1.0 / Signal_Denominator
      range -32_768.0 / Signal_Denominator .. 32_767.0 / Signal_Denominator;
   for Signal_Type'Small use 1.0 / Signal_Denominator;
   
   function Add_Signals (A : in Signal_Type; B : in Signal_Type) return
     Signal_Type
       with Pre => (A + B) > 0.0;
   
end FP_Test;
