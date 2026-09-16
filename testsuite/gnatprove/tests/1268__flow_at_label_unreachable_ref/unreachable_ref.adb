pragma Extensions_Allowed (All_Extensions);

procedure Unreachable_Ref
  (C : Integer; O : out Integer) with SPARK_Mode
is
   X : Integer;
begin
   <<Init>>
   X := C;

   if False then

      --  The following statement is unreachable. However, the 'At introduces
      --  an implicit object at a reachable label. Hence, the prefix (i.e., the
      --  implicit object) must still be analysed.

      O := X'At (Init);
   else
      O := 0;
   end if;
end Unreachable_Ref;
