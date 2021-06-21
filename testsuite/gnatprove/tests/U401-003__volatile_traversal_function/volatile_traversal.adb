procedure Volatile_Traversal with SPARK_Mode is
   type Int_Acc is access Integer;

   function Id_OK (X : access constant Integer) return access constant Integer is
     (X) with
     Volatile_Function;

   function Id_Bad (X : access Integer) return access Integer is
     (X) with
     Volatile_Function;
begin
   null;
end Volatile_Traversal;
