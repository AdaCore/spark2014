--  Yields synchronized object

with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;

package YSO with SPARK_Mode is

   --  Protected interface

   type Prot_Iface is protected interface;

   --  Protected type

   protected type Prot_Typ is
      entry Ent;
   end Prot_Typ;

   --  Synchronized interface

   type Sync_Iface is synchronized interface;

   --  Task interface

   type Task_Iface is task interface;

   --  Task type

   task type Task_Typ;

   --  Array type

   type Arr_Typ is array (1 .. 5) of Prot_Typ;

   --  Descendant of Suspension_Object

   type Sus_Obj is new Suspension_Object;

   --  Record type

   type Rec_Typ is record
      Comp_1 : Prot_Typ;
      Comp_2 : Task_Typ;
      Comp_3 : Arr_Typ;
      Comp_4 : Sus_Obj;
      Comp_5 : Suspension_Object;
   end record with Volatile;

   --  Type extension

--   type Root is tagged limited record
--      Comp_1 : Sus_Obj;
--   end record;

--   type Deriv_Typ_1 is new Root with null record;
--   type Deriv_Typ_2 is new Root with record
--      Comp_3 : Suspension_Object;
--   end record;

   type Deriv_Typ is new Rec_Typ;
end YSO;
