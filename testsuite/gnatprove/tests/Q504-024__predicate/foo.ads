package Foo
with SPARK_Mode
is

   type CPU_Range is range 0 .. 1;

   --  ID of the local CPU.
   CPU_ID : constant CPU_Range
   with
      Import,
      Convention => C,
      Link_Name  => "cpu_id";

   Max_LSID : constant := 5;

   type Max_LSID_Type is range 0 .. Max_LSID;

   type Per_CPU_LSID_Array is array (CPU_Range) of Max_LSID_Type;

   CPU_LSID_Last : constant Per_CPU_LSID_Array
     := (0 => 3,
         1 => 4);

   subtype Local_Subject_ID_Type is Max_LSID_Type
     with Dynamic_Predicate => Local_Subject_ID_Type <= CPU_LSID_Last (CPU_ID);

   type State_Array is array (Max_LSID_Type range <>) of Natural;

   type Subject_State (Max_ID : Max_LSID_Type) is record
      States : State_Array (0 .. Max_ID);
   end record;

   States : Subject_State (Max_ID => CPU_LSID_Last (CPU_ID));

   function Get_Element (ID : Local_Subject_ID_Type) return Natural
   is (States.States (ID));

   function Get_Elem_1 return Natural is (Get_Element (ID => 5));  --  @PREDICATE_CHECK:FAIL

   --  For the following line SPARK correctly issues a
   --  "predicate check might fail" warning.
   --  Var : constant Local_Subject_ID_Type := 5;

   function Get_Elem_2 return Natural is (States.States (5));

end Foo;
