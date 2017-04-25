pragma SPARK_Mode;

package body State
  with Refined_State => (State => S)
is

   procedure Test
     --  Uncomment either aspect to remove flow error
     --  with
     --  Refined_Global => (In_Out => S, Input => Foo.F)
     --  Refined_Depends => (S =>+ Foo.F)
   is
   begin
      S := S + Foo.Get;
   end Test;

end State;
