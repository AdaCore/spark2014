package body Search is

  procedure Linear_Search
    (Table : in IntArray;
     Value : in Integer;
     Found : out Boolean;
     Index : out Integer) is
  begin
     Found := False;
     Index := 0;

     for I in Integer range Table'Range loop
        pragma Assert (Found = False and
                       Counter < Integer'Last and
                       Counter = Counter'Old);
        if Table(I) = Value then
           Counter := Counter + 1;
           Found := True;
           Index := I;
           pragma Assert (Found and then Index = I);
           exit;
        end if;
     end loop;
  end Linear_Search;

  function Check_Index
    (Table : IntArray;
     Value : Integer;
     Index : Integer) return Boolean is
  begin
     return Table(Index) = Value;
  end Check_Index;

end Search;
