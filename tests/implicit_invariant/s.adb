package body S is

  procedure Linear_Search
    (Table : in IntArray;
     Value : in Integer;
     Found : out Boolean;
     Index : out Array_Range)
  is
  begin
     Found := False;
     Index := 1;

     for I in Array_Range range Table'Range loop
        if Table(I) = Value then
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
     Index : Array_Range) return Boolean
  is
  begin
     return Table(Index) = Value;
  end Check_Index;

end S;
