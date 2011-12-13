package S is

   type Array_Range is range 1 .. 10;

   type IntArray is array (Array_Range) of Integer;

   procedure Linear_Search
     (Table : in IntArray;
      Value : in Integer;
      Found : out Boolean;
      Index : out Array_Range)
   with Post => (not Found or else Table(Index) = Value);

   function Check_Index
     (Table : IntArray;
      Value : Integer;
      Index : Array_Range) return Boolean
   with Pre => (Table'First <= Index and then Index <= Table'Last),
        Post => (Check_Index'Result = (Table(Index) = Value));

end S;
