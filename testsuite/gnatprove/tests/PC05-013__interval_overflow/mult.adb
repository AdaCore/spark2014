procedure Mult
  with SPARK_Mode
is
   type Frame is range 0 .. 25_000;

   procedure Mars (N : Frame)
     with Pre => True
   is
   begin
      pragma Assert (N * 65 + 1 <= (N+1) * 65);
      pragma Assert (Float(N * 65 + 1) <= Float((N+1) * 65));
   end Mars;
begin
   Mars (10);
end Mult;
