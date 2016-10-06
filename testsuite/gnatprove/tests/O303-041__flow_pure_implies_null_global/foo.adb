with Ada.Numerics.Generic_Elementary_Functions;

procedure Foo (N : in out Float) is

   package FF is new Ada.Numerics.Generic_Elementary_Functions (Float);
   --  The generic unit Ada.Numerics.Generic_Elementary_Functions has pragma
   --  Pure, but this pragma applies only to the generic itself, not to the
   --  instance. In effect, flow analysis is still expected to warn that it is
   --  assuming Global => null on subprograms from this instance.

   --  ??? temporarily the above instantiation is rejected because the body of
   --  Generic_Elementary_Functions relies Long_Long_Float which is not
   --  supported in proof and conservatively rejected in marking. See PA03-024.

   use FF;

begin
   N := Log (N);
end Foo;
