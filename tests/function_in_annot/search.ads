package Search is

  type IntArray is array (Integer range <>) of Integer;

  function Table_Of_Index_Is_Value
    (Table : in IntArray;
     Value : in Integer;
     Index : in Integer) return Boolean;
  pragma Precondition (Table'First <= Index and then Index <= Table'Last);
  pragma Postcondition (Table_Of_Index_Is_Value'Result
                        = (Table(Index) = Value));

  procedure Dummy
    (Table : in IntArray;
     Value : in Integer;
     Index : in Integer);
  pragma Precondition (Table'First <= Index and then Index <= Table'Last
                       and then Table_Of_Index_Is_Value(Table, Index, Value));
  pragma Postcondition (Table(Index) = Value);

  procedure Reverse_Dummy
    (Table : in IntArray;
     Value : in Integer;
     Index : in Integer);
  pragma Precondition (Table'First <= Index and then Index <= Table'Last
                       and then Table(Index) = Value);
  pragma Postcondition (Table_Of_Index_Is_Value(Table, Index, Value));

  procedure Linear_Search
    (Table : in IntArray;
     Value : in Integer;
     Found : out Boolean;
     Index : out Integer);
  pragma Postcondition (not Found or else
                        Table_Of_Index_Is_Value(Table, Index, Value));

  function Check_Index
    (Table : IntArray;
     Value : Integer;
     Index : Integer) return Boolean;
  pragma Precondition (Table'First <= Index and then Index <= Table'Last);
  pragma Postcondition (Check_Index'Result =
                        Table_Of_Index_Is_Value(Table, Index, Value));

end Search;
