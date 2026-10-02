pragma Extensions_Allowed (On);

with SPARK.Pointers.Auto_Reclaimed.Immutable;
with SPARK.Pointers.Explicit_Reclamation.Global_Memory;
with SPARK.Pointers.Explicit_Reclamation.Separate_Memory;
with SPARK.Pointers.Poisoned.Views;

--  The generic actuals of the pointer library are checked inside the library
--  by instances of SPARK.Pointers.Parameter_Checks. Each instantiation below
--  supplies an actual that breaks the property one of those checks enforces,
--  so each must produce a failed check from inside the library.
--
--  The checks for absence of globals are in a separate test: flow analysis
--  rejects those outright, which stops the run before proof and would hide
--  everything here.

package Bad_Params with SPARK_Mode is

   --  A designated object that owns a cell

   type Int_Acc is access Integer;

   type Owning is record
      D : Int_Acc;
   end record;

   ---------------------------------------------------------------
   --  Is_Reclaimed_Checks: Is_Reclaimed shall only hold of a    --
   --  value that owes nothing. This one holds of every value.   --
   ---------------------------------------------------------------

   package Bad_Is_Reclaimed is new
     SPARK.Pointers.Explicit_Reclamation.Separate_Memory (Owning);

   --------------------------------------------------------------
   --  Reclamation_Checks: Reclaim shall reclaim its argument.  --
   --  The default actual is a null procedure, which does not.  --
   --------------------------------------------------------------

   package Bad_Reclaim is new
     SPARK.Pointers.Auto_Reclaimed.Immutable (Owning);

   ----------------------------------------------------------------
   --  Copy: nothing currently checks that it has no precondition --
   --  or reads no globals, so no check is expected from here.    --
   ----------------------------------------------------------------

   type Plain is record
      F : Integer;
   end record;

   function Is_Reclaimed (Unused : Plain) return Boolean is (True)
   with Ghost => Static;

   package Plain_Pointers is new
     SPARK.Pointers.Explicit_Reclamation.Global_Memory (Plain, Is_Reclaimed);

   function Copy_With_Pre (O : Plain) return Plain
   is (O)
   with Pre => O.F > 0;

   package Copy_Ops is new Plain_Pointers.Copy_Operations (Copy_With_Pre);

   -----------------------------------------------------------------
   --  Assignment_Checks: assignment shall preserve the object.    --
   --  It does not for a tagged type, whose hidden extension part  --
   --  is not carried by an assignment at the specific type.       --
   -----------------------------------------------------------------

   type Tagged_Object is tagged record
      F : Integer;
   end record;

   function Is_Reclaimed (Unused : Tagged_Object) return Boolean is (True)
   with Ghost => Static;

   package Bad_Assignment is new
     SPARK.Pointers.Poisoned.Views (Tagged_Object, Is_Reclaimed);

end Bad_Params;
