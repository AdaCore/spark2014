pragma Extensions_Allowed (On);

with SPARK.Pointers.Explicit_Reclamation.Global_Memory;

--  A generic actual of the pointer library that reads a global state is
--  rejected by flow analysis, because the library names it in the
--  postconditions of the operations that call it. Nothing extra is needed in
--  the library for this.
--
--  These cases live apart from 1448__pointers_parameter_checks because a
--  flow error stops the run before proof, which would hide every check
--  reported there.

package Global_Params with SPARK_Mode is

   State : Integer := 0;

   type Object is record
      F : Integer;
   end record;

   function Is_Reclaimed (Unused : Object) return Boolean is (State = 0)
   with Ghost => Static;

   package Pointers is new
     SPARK.Pointers.Explicit_Reclamation.Global_Memory (Object, Is_Reclaimed);

   ------------------------------------------------------------------
   --  Copy is named in the postconditions of Deref, Assign and    --
   --  Create_Copy, so a Copy that reads State is rejected there.  --
   ------------------------------------------------------------------

   function Copy_Reads_Global (Unused : Object) return Object
   is (F => State)
   with Global => State;

   package Copy_Ops is new Pointers.Copy_Operations (Copy_Reads_Global);

   ---------------------------------------------------------------
   --  Create_Object is named in the postcondition of Create, so --
   --  the same holds for it.                                    --
   ---------------------------------------------------------------

   function Create_Reads_Global (Unused : Integer) return Object
   is (F => State)
   with Global => State;

   procedure Create_From_Int is new
     Pointers.Create (Integer, Create_Reads_Global);

end Global_Params;
