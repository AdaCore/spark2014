pragma SPARK_Mode;

package Test with
  Abstract_State => State,
  Initializes => State
is

  procedure Test
    with Global => (In_Out => State);

private
   pragma SPARK_Mode (Off);

   N : Integer := 0
     with Part_Of => State;

end Test;
