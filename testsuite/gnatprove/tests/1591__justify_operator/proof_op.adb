package body Proof_Op with SPARK_Mode is

   ----------------
   -- By_Op_Name --
   ----------------

   function By_Op_Name (L, R : Integer) return Integer is
   begin
      return "&" (L, R) + 1;
      pragma Annotate (GNATprove, Intentional, """&"" (L, R)", "");
   end By_Op_Name;

   -------------------
   -- By_Check_Kind --
   -------------------

   function By_Check_Kind (L, R : Integer) return Integer is
   begin
      return "&" (L, R) + 1;
      pragma Annotate (GNATprove, Intentional, "overflow check might fail", "");
   end By_Check_Kind;
end;
