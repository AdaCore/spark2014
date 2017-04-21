pragma SPARK_Mode;

package State with
  Abstract_State => State,
  Initializes => State
is

   type State_Type is private;

   function Test1 return Integer
     with Ghost, Import, Global => State, Pre => True;

   function Test2 return Integer
     with Ghost, Import, Global => null, Pre => Test1 = Test1;

   function State return State_Type
     with Global => State;

   procedure Test with Ghost, Import;

private
   pragma SPARK_Mode (Off);

   type State_Type is new Integer;

   S : State_Type := 0
     with Part_Of => State;

end State;
