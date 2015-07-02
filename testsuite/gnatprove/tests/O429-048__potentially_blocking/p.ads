package P is

   Block : Boolean;

   procedure Potentially_Blocking_Proc;

   procedure Blocking_Proc;

   procedure Nonblocking_Proc;

   function Potentially_Blocking_Func return Boolean;

   function Blocking_Func return Boolean;

   function Nonblocking_Func return Boolean;

   protected type Nonblocking_Protected_Type is
      entry Nonblocking_Type_Entry;
      procedure Nonblocking_Type_Proc;
   end Nonblocking_Protected_Type;

   protected type Directly_Blocking_Protected_Type is
      entry Directly_Blocking_Type_Entry;
      procedure Directly_Blocking_Type_Proc;
   end Directly_Blocking_Protected_Type;

   protected type Indirectly_Blocking_Protected_Type is
      entry Indirectly_Blocking_Type_Entry;
      procedure Indirectly_Blocking_Type_Proc;
   end Indirectly_Blocking_Protected_Type;

   protected PO_1 is
      entry Nonblocking_Object_Entry;
      procedure Nonblocking_Object_Proc;
   end PO_1;

   protected PO_2 is
      entry Directly_Blocking_Object_Entry;
      procedure Directly_Blocking_Object_Proc;
   end PO_2;

   protected PO_3 is
      entry Indirectly_Blocking_Object_Entry;
      procedure Indirectly_Blocking_Object_Proc;
   end PO_3;

   protected PO_Stub_1 is
      entry Nonblocking_Stub_Entry;
      procedure Nonblocking_Stub_Proc;
   end PO_Stub_1;

   protected PO_Stub_2 is
      entry Directly_Blocking_Stub_Entry;
      procedure Directly_Blocking_Stub_Proc;
   end PO_Stub_2;

   protected PO_Stub_3 is
      entry Indirectly_Blocking_Stub_Entry;
      procedure Indirectly_Blocking_Stub_Proc;
   end PO_Stub_3;

   task type Blocking_Task_Type is
   end Blocking_Task_Type;

   task type Nonblocking_Task_Type is
   end Nonblocking_Task_Type;

end P;
