with Common;

package T is

   task type TT1 is
      pragma Priority (Common.Bad_Priority);
   end;

   task type TT2 is
      pragma Interrupt_Priority (Common.Bad_Interrupt_Priority);
   end;

   T1 : TT1;
   T2 : TT2;

end;
