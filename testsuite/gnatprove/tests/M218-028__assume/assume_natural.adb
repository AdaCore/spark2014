procedure Assume_Natural (X : Integer) is
begin
   pragma Assume (X in Natural);
   pragma Assert (X >= 0);
end Assume_Natural;
