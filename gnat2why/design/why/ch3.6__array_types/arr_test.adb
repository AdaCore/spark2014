package body Arr_Test is

  procedure Linear_Search
    (T     : Arr.Table;
     Value : Integer;
     Found : out Boolean;
     N     : out Arr.Index)
  is
     pragma Postcondition (not Found or else T (N) = Value);
  begin
     Found := False;
     N := Arr.Index'First;

     for I in T'Range loop
        pragma Assert (Found = False);
        if T (I) = Value then
           Found := True;
           N := I;
           pragma Assert (Found and then Integer (N) = Integer (I));
           exit;
        end if;
     end loop;
  end Linear_Search;

  function Check_Index
    (T     : Arr.Table;
     Value : Integer;
     N     : Arr.Index) return Boolean
  is
     pragma Postcondition (Check_Index'Result = (T (N) = Value));
  begin
     return T (N) = Value;
  end Check_Index;

end Arr_Test;
