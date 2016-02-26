procedure Bcheck is
   M2 : String (1 .. 10); -- big enough
   P  : Integer := 1;
begin
   M2 (P .. P + 4) := "12345";
end Bcheck;
