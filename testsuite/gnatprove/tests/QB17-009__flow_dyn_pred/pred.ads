with Data;

package Pred with Abstract_State => State, Elaborate_Body
is

private

   Values : constant Data.Value_Array := Data.Values
     with Part_Of => State;

   type Pair_Type is record
      Left : Integer range 0 .. 10;
      Right : Integer range 1 .. 10;
   end record
   with
     Predicate => Pair_Type.Left <= Values (Pair_Type.Right);

   Pair : Pair_Type := Pair_Type'(Left => 0, Right => 1)
     with Part_Of => State;

   Other : Integer := 0
     with Part_Of => State;

end Pred;
