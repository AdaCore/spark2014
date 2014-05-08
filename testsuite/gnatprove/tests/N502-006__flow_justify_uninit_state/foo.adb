package body Foo
  with Refined_State => (State => (Length, Data))
is
   type Length_T is range 0 .. 100;
   subtype Index_T is Length_T range 1 .. Length_T'Last;

   type Data_T is array (Index_T) of Integer;

   Length : Length_T;
   Data   : Data_T;

   procedure Init
     with Refined_Global => (Output => (Length, Data))
   is
   begin
      Length := 0;
   end Init;

end Foo;
