with Counter;

package body Use_Counter
  with SPARK_Mode
is

   procedure Run is
      Before : constant Natural := Counter.Value;
   begin
      Counter.Bump (0);
      --  The library's hidden state may have changed across the call to Bump,
      --  so the value read before the call cannot be assumed unchanged. This
      --  assertion is therefore not provable, which shows that GNATprove uses
      --  the global effects recorded in the installed summary ALI files.
      pragma Assert (Counter.Value = Before);
   end Run;

end Use_Counter;
