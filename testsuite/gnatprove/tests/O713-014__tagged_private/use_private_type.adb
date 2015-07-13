with Private_Types; use Private_Types;

procedure Use_Private_Type with SPARK_Mode is
   PR   : Root'Class := C;
   PR_D : Root_D'Class := C_D;
begin
   pragma Assert (PR in Root);
   pragma Assert (PR_D in Root_D);
end Use_Private_Type;
