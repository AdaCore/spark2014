package Tasks1 is

   task TA with Priority => 1;  --  @CEILING_PRIORITY_PROTOCOL:PASS
   task TB with Priority => 2;  --  @CEILING_PRIORITY_PROTOCOL:FAIL

end Tasks1;
