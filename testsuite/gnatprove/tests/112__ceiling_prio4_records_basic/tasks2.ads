package Tasks2 is

   --  Explicitly typed tasks

   task type TTA1 with Priority => 3;  --  @CEILING_PRIORITY_PROTOCOL:PASS
   task type TTA2 with Priority => 3;  --  @CEILING_PRIORITY_PROTOCOL:PASS
   task type TTB1 with Priority => 4;  --  @CEILING_PRIORITY_PROTOCOL:FAIL
   task type TTB2 with Priority => 4;  --  @CEILING_PRIORITY_PROTOCOL:FAIL

end Tasks2;
