procedure L (First, Last :     Integer;
             Low, High   :     Integer;
             Data        :     Boolean;
             Result      : out Boolean)
  with Depends => (Result => (Data, Low, High), null => (First, Last))
is
   subtype T is Integer range First .. Last;
   --  This subtype will only act as a constraint on the loop parameter;
   --  it will affect the values taken by this parameter and consequently
   --  the Result does not depend on First nor Last.
begin
   Result := False;
   for J in T range Low .. High loop
      Result := Result and Data and J = 1;
   end loop;
end;
