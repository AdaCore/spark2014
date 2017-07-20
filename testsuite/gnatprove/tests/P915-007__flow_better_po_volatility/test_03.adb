with System;

package body Test_03 with
   Refined_State => (State_N => null,
                     State_AWER => (PO_AW, PO_AR),
                     State_ER => PO_ER,
                     State_EW => PO_EW,
                     State_V  => PO_V)
is
   protected PO_AR is
   end PO_AR;
   protected PO_AW is
   end PO_AW;
   protected PO_ER is
   end PO_ER;
   protected PO_EW is
   end PO_EW;
   protected PO_V is
   end PO_V;

   V_AR : Integer with
     Volatile, Async_Readers,
     Import, Address => System'To_Address (16#DEADBEEF#),
     Part_Of => PO_AR;

   V_AW : Integer with
     Volatile, Async_Writers,
     Import, Address => System'To_Address (16#DEADBEEF#),
     Part_Of => PO_AW;

   V_ER : Integer with
     Volatile, Async_Writers, Effective_Reads,
     Import, Address => System'To_Address (16#DEADBEEF#),
     Part_Of => PO_ER;

   V_EW : Integer with
     Volatile, Async_Readers, Effective_Writes,
     Import, Address => System'To_Address (16#DEADBEEF#),
     Part_Of => PO_EW;

   V_V  : Integer with
     Volatile,
     Import, Address => System'To_Address (16#DEADBEEF#),
     Part_Of => PO_V;

   protected body PO_AR is
   end PO_AR;
   protected body PO_AW is
   end PO_AW;
   protected body PO_ER is
   end PO_ER;
   protected body PO_EW is
   end PO_EW;
   protected body PO_V is
   end PO_V;

end Test_03;
