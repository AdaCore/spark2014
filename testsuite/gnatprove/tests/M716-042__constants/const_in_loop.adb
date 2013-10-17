procedure Const_In_Loop (Z : out Positive) is
   V1, V2 : Integer := 1;
begin
   Z := 1;
   while True loop
     declare
        X : constant Integer := Z;
        subtype T is Positive range 1 .. Z;
     begin
        if Z = 1 then
           V1 := T'Last;
        end if;
        V2 := T'Last;
        pragma Assert (V1 = V2);
        pragma Loop_Invariant (V1 = T'Last);
        Z := 2;
     end;
   end loop;
end Const_In_Loop;
