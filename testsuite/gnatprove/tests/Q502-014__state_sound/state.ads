pragma SPARK_Mode;

package State with
  Abstract_State => State
is

   procedure Set (X : Integer)
     with Global => (In_Out => State),
          Post   => Get = X;

   function Get return Integer
     with Global => (Input => State);

private

   S1 : Integer range 0 .. 0 := 0
     with Part_Of => State;

end State;
