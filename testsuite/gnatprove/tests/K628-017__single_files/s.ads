package S is

   type Array_Range is range 1 .. 10;

   type IntArray is array (Array_Range) of Integer;

  function Contains (Table : IntArray; Value : Integer) return Boolean with
    Post => (if Contains'Result then (for some J in Table'Range => Table (J) = Value)
       else (for all J in Table'Range => Table (J) /= Value));

  procedure Move (Dest : out IntArray; Src : in out IntArray) with
    Post => (for all J in Dest'Range => Dest (J) = Src'Old (J));

end S;
