with Foo.PC.C;

package body Foo with
   Refined_State => (State_A => A,
                     State_B => PC.C.State),
   SPARK_Mode
is
   A : Boolean := False;

   procedure Do_Stuff (X : Boolean;
                       Y : out Boolean)
   with Global => (Input => A,
                   In_Out => PC.C.State)
   is
   begin
      PC.C.Wibble (A or X, Y);
   end Do_Stuff;

end Foo;
