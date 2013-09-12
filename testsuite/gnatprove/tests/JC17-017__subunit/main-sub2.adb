separate (Main)
procedure Sub2 (X : out Boolean) is  
   pragma Postcondition (not X);
begin
   X := False;
end;
