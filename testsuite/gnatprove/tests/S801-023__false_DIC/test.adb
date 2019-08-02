package body Test with
  SPARK_Mode
is

   procedure Initialize (Context : out Context_Type; First : Positive; Last : Positive) is
   begin
      Context := (First => First, Last => Last, Index => First);
   end Initialize;

   function Foo return Boolean is
      Context : Context_Type;  -- @DEFAULT_INITIAL_CONDITION:FAIL
   begin
      Initialize (Context, 1, 2);
      return Context.Index = 1;
   end Foo;

end Test;
