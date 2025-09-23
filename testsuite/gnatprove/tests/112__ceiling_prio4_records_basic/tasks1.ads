package Tasks1 is

   --  Anonymously typed tasks

   task TA1 with Priority => 3;  --  @CEILING_PRIORITY_PROTOCOL:PASS
   task TA2 with Priority => 3;  --  @CEILING_PRIORITY_PROTOCOL:PASS
   task TB1 with Priority => 4;  --  @CEILING_PRIORITY_PROTOCOL:FAIL
   task TB2 with Priority => 4;  --  @CEILING_PRIORITY_PROTOCOL:FAIL

end Tasks1;
