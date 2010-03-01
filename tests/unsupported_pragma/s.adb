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
     loop
        pragma Annotate (xcov, Exempt_On,
                           "The following decision fails MCDC;",
                           " we can justify why it is harmless.");
        pragma Assert (Found = False);
        pragma Annotate (xcov, Exempt_Off);
        if Table(Index) = Value then
           Found := True;
           exit;
        end if;

        exit when Index = Array_Range'(Table'Last);
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
