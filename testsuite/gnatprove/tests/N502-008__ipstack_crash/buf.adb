package body Buf with
  SPARK_Mode,
  Refined_State => (State => null)
is

   procedure P is null;
   --  dummy procedure to force a body
end Buf;
