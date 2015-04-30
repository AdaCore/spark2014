with Pure_Package;
with Impure_Package;
with Impure_Procedure;
with Ada.Numerics.Elementary_Functions;

procedure Call
  with Global => null
is
   X : Integer := 0;
begin
   --  Log is assumed to have aspect Global => null, because
   --  Ada.Numerics.Elementary_Function is an internal file.
   X := Integer (Ada.Numerics.Elementary_Functions.Log (0.0));

   --  These calls should also be assumed to have aspect Global => null,
   --  because of SPARK RM 6.1.4 (4), i.e.,

   --  the subprogram is a library-level subprogram declared in a library unit
   --  that is declared pure
   X := Pure_Package.Pure_Function (X);

   X := Impure_Package.Impure_Function (X);

   --  a Impure_Function pragma applies to the subprogram
   Impure_Procedure (X);

   --  These implicit assumptions should be verified when analyzing these
   --  subprograms.
end Call;
