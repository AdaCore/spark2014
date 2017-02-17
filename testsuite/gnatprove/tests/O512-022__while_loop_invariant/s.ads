package S is

   type Array_Range is range 1 .. 10;

   type IntArray is array (Array_Range) of Integer;

   procedure Linear_Search
     (Table : in IntArray;
      Value : in Integer;
      Found : out Boolean;
      Index : out Array_Range);
   pragma Postcondition (not Found or else Table(Index) = Value);

   function Check_Index
     (Table : IntArray;
      Value : Integer;
      Index : Array_Range) return Boolean;
   pragma Precondition (Table'First <= Index and then Index <= Table'Last);
   pragma Postcondition (Check_Index'Result = (Table(Index) = Value));

end S;
