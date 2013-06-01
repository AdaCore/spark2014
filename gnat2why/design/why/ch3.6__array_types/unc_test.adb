package body Unc_Test is

  procedure Linear_Search
    (Table : in Vector;
     Value : in Integer;
     Found : out Boolean;
     Index : out Integer)
  is
     pragma Postcondition (not Found or else Table(Index) = Value);
  begin
     Found := False;
     Index := 0;

     for I in Integer range Table'Range loop
        pragma Assert (Found = False);
        if Table(I) = Value then
           Found := True;
           Index := I;
           pragma Assert (Found and then Index = I);
           exit;
        end if;
     end loop;
  end Linear_Search;

  function Check_Index
    (Table : Vector;
     Value : Integer;
     Index : Integer) return Boolean
  is
     pragma Postcondition (Check_Index'Result = (Table(Index) = Value));
  begin
     return Table(Index) = Value;
  end Check_Index;

end Unc_Test;
