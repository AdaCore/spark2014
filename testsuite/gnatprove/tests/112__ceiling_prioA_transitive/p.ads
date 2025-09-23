package P is

   protected PO1
     with Priority => 10
   is
      procedure PP11;  --  @CEILING_PRIORITY_PROTOCOL:PASS
   end;

   procedure PA;

   protected PO2
     with Priority => 10
   is
      procedure PP21;  --  @CEILING_PRIORITY_PROTOCOL:FAIL
   end;

   procedure PB;

   protected PO3
     with Priority => 5
   is
      procedure PP31;
   end;

end P;
