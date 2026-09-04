pragma Extensions_Allowed (All_Extensions);

procedure Unreachable_Ref
  (C : Integer; O : out Integer) with SPARK_Mode
is
   X : Integer;
begin
   <<Init>>
   X := C;

   --  Reference to X'At (Init) is not reachable
   if False then
      O := X'At (Init);
   else
      O := 0;
   end if;
end Unreachable_Ref;
