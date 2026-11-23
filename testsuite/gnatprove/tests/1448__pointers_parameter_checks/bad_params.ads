pragma Extensions_Allowed (On);

with SPARK.Pointers.Auto_Reclaimed.Immutable;
with SPARK.Pointers.Explicit_Reclamation.Global_Memory;
with SPARK.Pointers.Explicit_Reclamation.Separate_Memory;
with SPARK.Pointers.Parameter_Checks;
with SPARK.Pointers.Poisoned.Pointers;
with SPARK.Pointers.Poisoned.Pointers.Array_Operations;
with SPARK.Pointers.Poisoned.Views;
with SPARK.Pointers.Poisoned.Views.Array_Operations;

--  The generic actuals of the pointer library are checked inside the library
--  by instances of SPARK.Pointers.Parameter_Checks. The negative cases below
--  supply actuals that must produce failed checks from inside the library.
--  Ordinary array instances provide positive cases for the array checks.
--
--  The checks for absence of globals are in a separate test: flow analysis
--  rejects those outright, which stops the run before proof and would hide
--  everything here.

package Bad_Params with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

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
   --  Copy must accept every value of the designated type.      --
   --  This actual requires a positive component instead.        --
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

   package Copy_Ops is new Plain_Pointers.Copy_Operations (Copy_With_Pre); -- @PRECONDITION:FAIL

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

   --  Array_Checks: array types shall admit the same component states and
   --  bounds as ordinary arrays. Check ordinary arrays as well as arrays
   --  with restrictive predicates or relaxed initialization.

   package P is new SPARK.Pointers.Poisoned.Pointers (Integer);
   use type P.Pointer;
   type Pointers is array (Positive range <>) of P.Pointer;
   package Plain_Pointer_Arrays is new P.Array_Operations (Positive, Pointers);

   type Restricted is array (Positive range <>) of P.Pointer
     with Dynamic_Predicate =>
       (if Restricted'Length > 0
        then Restricted (Restricted'First) = P.Null_Pointer);
   package Restricted_Pointers is new P.Array_Operations (Positive, Restricted);

   package V is new SPARK.Pointers.Poisoned.Views (Integer);
   use V;
   type Objects is array (Positive range <>) of aliased Integer;
   package Plain_Views is new V.Array_Operations (Positive, Objects);

   type Based_At_One is array (Positive range <>) of aliased Integer
     with Dynamic_Predicate => Based_At_One'First = 1;
   package Restricted_Views is new V.Array_Operations (Positive, Based_At_One);

   type Relaxed is array (Positive range <>) of Integer
     with Relaxed_Initialization;
   package Relaxed_Check is new SPARK.Pointers.Parameter_Checks.Array_Checks
     (Positive, Integer, Relaxed);

end Bad_Params;
