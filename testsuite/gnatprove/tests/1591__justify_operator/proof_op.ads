package Proof_Op with SPARK_Mode is
   function "&" (L, R : Integer) return Integer with Import, Global => null;
   function By_Op_Name (L, R : Integer) return Integer;
   function By_Check_Kind (L, R : Integer) return Integer;
end Proof_Op;
