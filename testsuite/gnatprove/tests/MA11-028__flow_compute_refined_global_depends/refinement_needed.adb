package body Refinement_Needed
  with Refined_State => (State  => A,
                         State2 => null)
is
   A : Integer := 0;

   function Foo return Integer is
   begin
      return A;
   end Foo;

   function Bar return Integer is
   begin
      return V1 + V2;
   end Bar;

   function Hmmm return Integer is
   begin
      if Other.Wibble then
         return 1;
      else
         return 0;
      end if;
   end Hmmm;
end Refinement_Needed;
