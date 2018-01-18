with Pure_Spec;
with Impure_Spec;

with Ada.Numerics.Elementary_Functions;

with Pure_Package;
with Impure_Package;

procedure Call
  with Global => null
is
   X : Integer := 0;
begin
   --  For these we have no bodies, but we silently assume Global => null
   --  without caring about the pragma Pure
   X := Pure_Spec.Pure_Function (X);
   X := Impure_Spec.Impure_Function (X);

   --  Log is silently assumed to have aspect Global => null, because
   --  Ada.Numerics.Elementary_Function is an internal file and
   --  is declared as pure.
   X := Integer (Ada.Numerics.Elementary_Functions.Log (0.0));

   --  These calls should also be assumed to have aspect Global => null,
   --  because of SPARK RM 6.1.4 (4), i.e., a library-level subprogram declared
   --  in a library unit declared as pure
   X := Pure_Package.Pure_Function (X);
   X := Impure_Package.Pure_Function (X);

   --  These implicit assumptions should be verified when analyzing these
   --  subprograms.
end Call;
