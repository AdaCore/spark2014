with Ada.Containers.Indefinite_Hashed_Maps;
with Ada.Strings.Hash;
with GPR2; use GPR2;
with GPR2.Build.Compilation_Unit;
with GPR2.Project.Tree;
with String_Utils;

package Gnatprove_Build is

   --  This package contains types and subprograms related to the
   --  build process of Gnatprove.

   package Unit_Maps is new
     Ada.Containers.Indefinite_Hashed_Maps
       (Key_Type        => String,
        Element_Type    => GPR2.Build.Compilation_Unit.Object,
        Hash            => Ada.Strings.Hash,
        Equivalent_Keys => "=",
        "="             => GPR2.Build.Compilation_Unit."=");

   subtype Unit_Set is Unit_Maps.Map;
   --  A set of compilation units. Units are keyed internally by a stable key
   --  so that they stay distinct across aggregate project roots.

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
