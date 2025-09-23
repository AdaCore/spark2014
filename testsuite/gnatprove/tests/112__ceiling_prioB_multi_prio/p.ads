with System;
with Ada.Interrupts.Names; use Ada.Interrupts.Names;

package P is
   protected type PT1 with Priority => 1 is
      procedure Proc1;
   end;

   protected type PT2 is
      procedure Proc2;
   end;

   protected type PT3
     with Interrupt_Priority => System.Interrupt_Priority'Last
   is
      procedure Proc3;
   end;

   type T is record
      C1 : PT1;
      C2 : PT2;
      C3 : PT3;
      C4 : PT1;
   end record;

   X : T;
end;
