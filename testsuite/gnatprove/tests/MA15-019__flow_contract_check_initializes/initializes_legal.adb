package body Initializes_Legal
  with SPARK_Mode,
       Refined_State => (AS => (Y, Z))
is
   Z : Integer;
   Y : Integer := Init.Sum_State;

   procedure Does_Nothing is begin null; end Does_Nothing;
begin
   Z := 0;
end Initializes_Legal;
