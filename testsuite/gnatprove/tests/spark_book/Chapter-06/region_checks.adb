pragma SPARK_Mode(On);

package body Region_Checks is

   function Sign (X : in Integer) return Sign_Type is
   begin
      case X is
         when Integer'First .. -1 => return -1;
         when 0 => return 0;
         when 1 .. Integer'Last => return 1;
      end case;
   end Sign;


   function In_Unit_Square (X, Y : in Integer) return Sign_Type is
   begin
      if X in -1 .. 1 and Y in -1 .. 1 then
         -- In the square.
         return 1;
      elsif X >= 0 and Y >= 0 then
         -- First quadrant.
         return 0;
      elsif X < 0 and Y >= 0 then
         -- Second quadrant.
         return -1;
      elsif X < 0 and Y < 0 then
         -- Third quadrant.
         return 0;
      else
         -- Forth quadrant.
         return -1;
      end if;
   end In_Unit_Square;

end Region_Checks;
