package body S is

  procedure Linear_Search
    (Table : in IntArray;
     Value : in Integer;
     Found : out Boolean;
     Index : out Array_Range)
  is
  begin
     Found := False;

     Index := Table'First;
     while Index <= Array_Range'(Table'Last) loop
        pragma Loop_Invariant (Found = False);
        if Table(Index) = Value then
           Found := True;
           exit;
        end if;

        if Index = Table'Last then
           exit;
        end if;

        Index := Index + 1;
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
