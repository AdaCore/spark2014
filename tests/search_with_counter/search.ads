package Search
--# own Counter;
--# initializes Counter;
is

  type IntArray is array (Integer range <>) of Integer;

  Counter : Natural := 0;

  procedure Linear_Search
    (Table : in IntArray;
     Value : in Integer;
     Found : out Boolean;
     Index : out Integer);
  pragma Precondition (Counter < Integer'Last);
  pragma Postcondition (not Found or else
                          ((Table(Index) = Value) and then
                           Counter = Counter'Old + 1));

  function Check_Index
    (Table : IntArray;
     Value : Integer;
     Index : Integer) return Boolean;
  pragma Precondition (Table'First <= Index and then Index <= Table'Last);
  pragma Postcondition (Check_Index'Result = (Table(Index) = Value));

end Search;
