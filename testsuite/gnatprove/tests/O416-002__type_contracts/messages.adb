package body Messages
  with SPARK_Mode
is
   procedure Process (M : in out Message) is
   begin
      M := (Sent => M.Received, Received => M.Sent);
   end Process;

end Messages;
