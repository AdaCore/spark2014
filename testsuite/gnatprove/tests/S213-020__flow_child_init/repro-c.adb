with Repro.B; pragma Elaborate (Repro, Repro.B);

package body Repro.C
with Refined_State => (CState => Y)
is

   Y : Byte := Get_Foo;

   procedure Baz
   with Refined_Global => (In_Out => (Y, Repro.State))
   is
   begin
      B.Bar;

      Y := Y + 1;
   end Baz;

end Repro.C;
