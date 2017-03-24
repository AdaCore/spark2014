package body Foo

with SPARK_Mode => Off,
  Refined_State => (State => Dummy)
is

   Dummy : Integer;

   procedure Initialize
   is
   begin
      null;
   end;

end;
