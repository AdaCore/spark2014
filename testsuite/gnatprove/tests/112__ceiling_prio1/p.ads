package P is

   protected PO1
     with Priority => 4
   is
      procedure PP11;
   end;

   procedure P2;

   protected PO2
     with Priority => 3
   is
      procedure PP21;  --  @CEILING_PRIORITY_PROTOCOL:FAIL
   end;

   procedure P3;

   protected PO3
     with Priority => 2
   is
      procedure PP31;  --  @CEILING_PRIORITY_PROTOCOL:FAIL
   end;
   procedure P4;

   protected PO4
     with Priority => 1
   is
      procedure PP41;
   end;

end P;
