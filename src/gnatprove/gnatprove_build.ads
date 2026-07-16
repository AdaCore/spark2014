with Ada.Containers; use Ada.Containers;
with Ada.Containers.Indefinite_Hashed_Sets;
with GPR2;           use GPR2;
with GPR2.Build.Compilation_Unit;
with GPR2.Project.Tree;
with String_Utils;

package Gnatprove_Build is

   --  This package contains types and subprograms related to the
   --  build process of Gnatprove.

   function Unit_Hash
     (Unit : GPR2.Build.Compilation_Unit.Object) return Hash_Type;
   function Unit_Equal
     (Left, Right : GPR2.Build.Compilation_Unit.Object) return Boolean;
   --  Hash and equivalence for compilation units. Both are based on a stable
   --  key (main source path plus index) rather than the unit name, so that
   --  units stay distinct across aggregate project roots, where names are not
   --  unique.

   package Unit_Sets is new
     Ada.Containers.Indefinite_Hashed_Sets
       (Element_Type        => GPR2.Build.Compilation_Unit.Object,
        Hash                => Unit_Hash,
        Equivalent_Elements => Unit_Equal,
        "="                 => GPR2.Build.Compilation_Unit."=");

   subtype Unit_Set is Unit_Sets.Set;
   --  A set of compilation units

   procedure Flow_Analysis_And_Proof
     (Tree              : Project.Tree.Object;
      SPARK_Error_Files : out String_Utils.String_Lists.List;
      Analyzed_Units    : out Unit_Set;
      Success           : out Boolean);
   --  Call gnat2why on all relevant units in analysis mode, generating
   --  unit.spark files. Analyzed_Units is set to the units for which an
   --  analysis action was queued; a unit's .spark file may be absent if its
   --  action failed at runtime, so consumers must check existence before use.
   --  SPARK_Error_Files is set to the expected .spark_error file paths (one
   --  per queued global-generation action); these carry frontend diagnostics
   --  for the report. Success is set to False if analysis failed.

end Gnatprove_Build;
