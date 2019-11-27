package body Repro
with
   Refined_State => (State => Some_Var)
is
   pragma Warnings (Off, """Some_Var"" is not modified, could be declared constant");
   Some_Var : Natural := 0;
   pragma Warnings (On, """Some_Var"" is not modified, could be declared constant");

   procedure Foo (Value : out Natural)
   with
      Refined_Global  => (Input => Some_Var),
      Refined_Depends => (Value => Some_Var)
   is
      pragma Annotate
         (GNATprove, Intentional,
          "incorrect dependency ""Value => Some_Var constituent of State""",
          "Derived through DMA.");
   begin
      Value := 42;
   end Foo;
end Repro;
