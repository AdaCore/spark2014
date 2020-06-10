package body Foo with
  SPARK_Mode
is

   procedure Initialize (Context : out Context_Type) is
   begin
      Context := (X => 11);
   end Initialize;

   function Valid (Context : Context_Type) return Boolean is
     (Valid_X (Context.X));

end Foo;
