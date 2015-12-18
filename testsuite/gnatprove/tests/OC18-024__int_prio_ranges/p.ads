with Common;

package P is

   protected type PT1 is
      pragma Priority (Common.Bad_Priority);
   end;

   protected type PT2 is
      pragma Interrupt_Priority (Common.Bad_Interrupt_Priority);
   end;

   PO1 : PT1;
   PO2 : PT2;

end;
