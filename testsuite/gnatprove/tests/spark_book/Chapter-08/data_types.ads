
package Data_Types is
   type Time_Type is private;
   function Time_Initializer return Time_Type;

   type Temperature_Type is range 0 .. 2**12 - 1;  -- 12 bit ADC output.

private
   type Time_Type is new Integer;  -- Place holder
end Data_Types;
