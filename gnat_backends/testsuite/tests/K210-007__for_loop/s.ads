package S is

   type Array_Range is range 1 .. 10;

   type IntArray is array (Array_Range) of Integer;

  function Contains (Table : IntArray; Value : Integer) return Boolean with
    Post => (for some J in Table'Range => Table (J) = Value);

  procedure Move (Dest, Src : out IntArray) with
    Post => (for all J in Dest'Range => Dest (J) = Src'Old (J));

end S;
