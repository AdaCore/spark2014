pragma SPARK_Mode(On);

package Region_Checks is
   subtype Sign_Type is Integer range -1 .. 1;

   function Sign (X : in Integer) return Sign_Type
     with
       Contract_Cases =>
         (X < 0 => Sign'Result = -1,
          X = 0 => Sign'Result =  0,
          X > 0 => Sign'Result =  1);

   function In_Unit_Square (X, Y : in Integer) return Sign_Type
     with
       Contract_Cases =>
         (X >= 0 and Y >= 0 and not(X <=  1 and Y <=  1) =>
                  In_Unit_Square'Result =  0,
          X <  0 and Y >= 0 and not(X >= -1 and Y <=  1) =>
                  In_Unit_Square'Result = -1,
          X <  0 and Y <  0 and not(X >= -1 and Y >= -1) =>
                  In_Unit_Square'Result =  0,
          X >= 0 and Y <  0 and not(X <=  1 and Y >= -1) =>
                  In_Unit_Square'Result = -1,
          others => In_Unit_Square'Result = 1);

end Region_Checks;
