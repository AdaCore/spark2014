package body Search is

  procedure Linear_Search
    (Table  : in IntArray;
     Value1 : in Integer;
     Value2 : in Integer;
     Found1 : out Boolean;
     Found2 : out Boolean;
     Index1 : out Integer;
     Index2 : out Integer)
  is
     Found : Natural := 0;
  begin
     Found1 := False;
     Index1 := 0;
     Found2 := False;
     Index2 := 0;

     for I in Integer range Table'Range loop
        pragma Assert ((Found = 0 and not Found1 and not Found2) or else
                       (Found = 1 and (Found1 or Found2)) or else
                       (Found = 2 and Found1 and Found2));
        pragma Assert (Found1 = False or else Found2 = False);
        pragma Assert (not Found1 or else Table(Index1) = Value1);
        pragma Assert (not Found2 or else Table(Index2) = Value2);
        pragma Assert (Found < 2);
        if not Found1 and then Table(I) = Value1 then
           Found1 := True;
           Index1 := I;
           Found := Found + 1;
           pragma Assert (Found1 and then Index1 = I);
           pragma Assert (Found <= 2);
        end if;
        if not Found2 and then Table(I) = Value2 then
           Found2 := True;
           Index2 := I;
           Found := Found + 1;
           pragma Assert (Found2 and then Index2 = I);
           pragma Assert (Found <= 2);
        end if;
        exit when Found = 2;
     end loop;
  end Linear_Search;

  function Check_Index
    (Table  : IntArray;
     Value1 : Integer;
     Value2 : Integer;
     Index1 : Integer;
     Index2 : Integer) return Boolean
  is
  begin
     return Table(Index1) = Value1 and then Table(Index2) = Value2;
  end Check_Index;

end Search;
