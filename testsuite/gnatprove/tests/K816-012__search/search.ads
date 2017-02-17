package Search is

  type IntArray is array (Integer range <>) of Integer;

  procedure Linear_Search
    (Table  : in IntArray;
     Value1 : in Integer;
     Value2 : in Integer;
     Found1 : out Boolean;
     Found2 : out Boolean;
     Index1 : out Integer;
     Index2 : out Integer);
  pragma Postcondition (not Found1 or else Table(Index1) = Value1);
  pragma Postcondition (not Found2 or else Table(Index2) = Value2);

  function Check_Index
    (Table  : IntArray;
     Value1 : Integer;
     Value2 : Integer;
     Index1 : Integer;
     Index2 : Integer) return Boolean;
  pragma Precondition (Table'First <= Index1 and then Index1 <= Table'Last);
  pragma Precondition (Table'First <= Index2 and then Index2 <= Table'Last);
  pragma Postcondition (Check_Index'Result = (Table(Index1) = Value1 and then
                                                Table(Index2) = Value2));

end Search;
