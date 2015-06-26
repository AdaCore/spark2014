with Ada.Real_Time;

package body P is

   Now : Ada.Real_Time.Time := Ada.Real_Time.Clock;

   procedure Potentially_Blocking_Proc is
   begin
      if Block then
         delay until Now;
      end if;
   end Potentially_Blocking_Proc;

   procedure Blocking_Proc is
   begin
      delay until Now;
   end Blocking_Proc;

   procedure Nonblocking_Proc is
   begin
      null;
   end Nonblocking_Proc;

   function Potentially_Blocking_Func return Boolean is
   begin
      if Block then
         delay until Now;
      end if;
      return True;
   end Potentially_Blocking_Func;

   function Blocking_Func return Boolean is
   begin
      delay until Now;
      return True;
   end Blocking_Func;

   function Nonblocking_Func return Boolean is
   begin
      return True;
   end Nonblocking_Func;

   protected body Nonblocking_Protected_Type is
      entry Dummy when True is
      begin
         null;
      end Dummy;
   end Nonblocking_Protected_Type;

   protected body Blocking_Protected_Type is
      entry Dummy when True is
      begin
         delay until Now;
      end Dummy;
   end Blocking_Protected_Type;

   Nonblocking_Protected_Object : Nonblocking_Protected_Type;
   Blocking_Protected_Object : Blocking_Protected_Type;

   protected body PO_1 is
      entry Nonblocking_Entry when True is
      begin
         null;
      end Nonblocking_Entry;
   end PO_1;

   protected body PO_2 is
      entry Blocking_Entry when True is
      begin
         delay until Now;
      end Blocking_Entry;
   end PO_2;

   protected body PO_Stub_1 is separate;
   protected body PO_Stub_2 is separate;

   task body Blocking_Task_Type is
   begin
      delay until Now;
   end Blocking_Task_Type;

   task body Nonblocking_Task_Type is
   begin
      null;
   end Nonblocking_Task_Type;

   Blocking_Task : Blocking_Task_Type;
   Nonblocking_Task : Nonblocking_Task_Type;

end P;
