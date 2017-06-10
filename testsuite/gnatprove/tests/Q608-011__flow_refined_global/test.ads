with Prop;
with Values;

package Test
with
   Ghost,  --  must be ghost to trigger error
   Abstract_State => State
is

   procedure Inc
   with
      Global => (In_Out => State,
                 Input => Values.Val);

private

   T : Integer := 0 with Part_Of => State;

end Test;
