with Ada.Dispatching;
with Ada.Text_IO;
with Ada.Real_Time;
with Ada.Numerics.Elementary_Functions;

with Remote, Barrier, Complex, Floatio;

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

   protected body PO_4 is
      entry Yielding_Entry when True is
      begin
         Yielding_Proc;
      end Yielding_Entry;

      procedure Yielding_Proc is
      begin
         Ada.Dispatching.Yield;
      end Yielding_Proc;
   end;

   protected body PO_5 is
      entry Pure_Entry when True is
      begin
         Pure_Proc;
      end Pure_Entry;

      procedure Pure_Proc is
         X : Float;
      begin
         X := Ada.Numerics.Elementary_Functions.Sin (0.0);
      end Pure_Proc;
   end;

   protected body PO_6 is
      entry Remote_Entry when True is
      begin
         Remote_Proc;
      end Remote_Entry;

      procedure Remote_Proc is
      begin
         Remote.Remote_Call;
      end Remote_Proc;
   end;

   protected body PO_7 is
      entry Barrier_Entry when True is
      begin
         Barrier_Proc;
      end Barrier_Entry;

      procedure Barrier_Proc is
      begin
         Barrier.Wait;
      end Barrier_Proc;
   end;

   protected body PO_8 is
      entry File_Entry when True is
      begin
         File_Proc;
      end File_Entry;

      procedure File_Proc is
         F : Ada.Text_IO.File_Type;
      begin
         Ada.Text_IO.Open (F, Ada.Text_IO.In_File, "dummy.txt");
      end File_Proc;
   end;

   protected body PO_9 is
      entry Text_Entry when True is
      begin
         Text_Proc;
      end Text_Entry;

      procedure Text_Proc is
      begin
         Ada.Text_IO.Put_Line ("dummy");
      end Text_Proc;
   end;

   protected body PO_10 is
      entry My_Text_Entry when True is
         subtype My_Float is Float range 0.0 .. 1.0;

         package My_Float_Text_IO is new Ada.Text_IO.Float_IO (My_Float);
      begin
         My_Float_Text_IO.Put (My_Float'First);
      end;

   end;

   protected body PO_11 is
      entry Complex_Print_Entry when True is
      begin
         Complex;
      end;

   end;

   protected body PO_12 is
      entry Floatio_Print_Entry when True is
      begin
         Floatio;
      end;

   end;

end P;
