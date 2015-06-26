package P is

   Block : Boolean;

   procedure Potentially_Blocking_Proc;

   procedure Blocking_Proc;

   procedure Nonblocking_Proc;

   function Potentially_Blocking_Func return Boolean;

   function Blocking_Func return Boolean;

   function Nonblocking_Func return Boolean;

   protected type Nonblocking_Protected_Type is
      entry Dummy;
   end Nonblocking_Protected_Type;

   protected type Blocking_Protected_Type is
      entry Dummy;
   end Blocking_Protected_Type;

   protected PO_1 is
      entry Nonblocking_Entry;
   end PO_1;

   protected PO_2 is
      entry Blocking_Entry;
   end PO_2;

   protected PO_Stub_1 is
      entry Nonblocking_Entry;
   end PO_Stub_1;

   protected PO_Stub_2 is
      entry Blocking_Entry;
   end PO_Stub_2;

   task type Blocking_Task_Type is
   end Blocking_Task_Type;

   task type Nonblocking_Task_Type is
   end Nonblocking_Task_Type;

end P;
