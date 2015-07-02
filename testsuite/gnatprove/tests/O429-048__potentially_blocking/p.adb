with Ada.Real_Time;

package body P is

   Now : Ada.Real_Time.Time := Ada.Real_Time.Clock;

   --  Helper procedures

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

   --  Helper functions

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

   --  Protected types

   protected body Nonblocking_Protected_Type is
      entry Nonblocking_Type_Entry when True is
      begin
         null;
      end Nonblocking_Type_Entry;

      procedure Nonblocking_Type_Proc is
      begin
         null;
      end Nonblocking_Type_Proc;
   end Nonblocking_Protected_Type;

   protected body Directly_Blocking_Protected_Type is
      entry Directly_Blocking_Type_Entry when True is
      begin
         delay until Now;
      end Directly_Blocking_Type_Entry;

      procedure Directly_Blocking_Type_Proc is
      begin
         delay until Now;
      end Directly_Blocking_Type_Proc;
   end Directly_Blocking_Protected_Type;

   protected body Indirectly_Blocking_Protected_Type is
      entry Indirectly_Blocking_Type_Entry when True is
      begin
         Blocking_Proc;
      end Indirectly_Blocking_Type_Entry;

      procedure Indirectly_Blocking_Type_Proc is
      begin
         Blocking_Proc;
      end Indirectly_Blocking_Type_Proc;
   end Indirectly_Blocking_Protected_Type;

   Nonblocking_Protected_Object : Nonblocking_Protected_Type;
   Directly_Blocking_Protected_Object : Directly_Blocking_Protected_Type;
   Indirectly_Blocking_Protected_Object : Indirectly_Blocking_Protected_Type;

   --  Protected objects

   protected body PO_1 is
      entry Nonblocking_Object_Entry when True is
      begin
         null;
      end Nonblocking_Object_Entry;

      procedure Nonblocking_Object_Proc is
      begin
         null;
      end Nonblocking_Object_Proc;
   end PO_1;

   protected body PO_2 is
      entry Directly_Blocking_Object_Entry when True is
      begin
         delay until Now;
      end Directly_Blocking_Object_Entry;

      procedure Directly_Blocking_Object_Proc is
      begin
         delay until Now;
      end Directly_Blocking_Object_Proc;
   end PO_2;

   protected body PO_3 is
      entry Indirectly_Blocking_Object_Entry when True is
      begin
         Blocking_Proc;
      end Indirectly_Blocking_Object_Entry;

      procedure Indirectly_Blocking_Object_Proc is
      begin
         Blocking_Proc;
      end Indirectly_Blocking_Object_Proc;
   end PO_3;

   --  Protected stubs

   protected body PO_Stub_1 is separate;
   protected body PO_Stub_2 is separate;
   protected body PO_Stub_3 is separate;

   --  Tasks (sanity checking)

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
