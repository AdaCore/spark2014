pragma SPARK_Mode(On);
package Tank1
  with
    Abstract_State => Tank_State

is

   function Valid_Sensors return boolean
     with
       Global  => (Input => Tank_State),
       Depends => (Valid_Sensors'Result => Tank_State);

   function Valid_Tank return boolean
     with
       Global  => (Input => Tank_State),
       Depends => (Valid_Tank'Result => Tank_State),
       Ghost;
end;
