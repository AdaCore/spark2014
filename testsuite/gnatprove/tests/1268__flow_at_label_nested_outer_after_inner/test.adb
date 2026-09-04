pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2 : Integer) with SPARK_Mode is
   X : Integer := C1;
begin
   <<Outer>>
   X := C2;
   <<Inner>>
   null;
   pragma Assert (X'At (Outer)'At (Inner) = C1);
end Test;
