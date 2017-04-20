pragma SPARK_Mode;

package State with
  Abstract_State => State
is

   type State_Type is private;

   function State return State_Type
     with Global => State;
   
   procedure Test
     with Pre => True;

private
   pragma SPARK_Mode (Off);

   type State_Type is new Integer;

   S : State_Type := 0
     with Part_Of => State;

end State;
