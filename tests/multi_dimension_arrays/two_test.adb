package body Two_Test is

  procedure Linear_Search
    (T     : Two.Table;
     Value : Integer;
     Found : out Boolean;
     I1    : out Two.Index;
     I2    : out Two.Index)
  is
     pragma Postcondition (not Found or else T (I1, I2) = Value);
  begin
     Found := False;
     I1 := Two.Index'First;
     I2 := Two.Index'First;

     for J1 in T'Range (1) loop
        pragma Assert (Found = False);
        for J2 in T'Range (2) loop
           pragma Assert (Found = False);
           if T (I1, I2) = Value then
              Found := True;
              I1 := J1;
              I2 := J2;
              return;
           end if;
        end loop;
     end loop;
  end Linear_Search;

  function Check_Index
    (T     : Two.Table;
     Value : Integer;
     I1    : Two.Index;
     I2    : Two.Index) return Boolean
  is
     pragma Postcondition (Check_Index'Result = (T (I1, I2) = Value));
  begin
     return T (I1, I2) = Value;
  end Check_Index;

end Two_Test;
