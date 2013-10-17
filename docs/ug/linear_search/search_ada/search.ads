pragma SPARK_Mode;

package Search is

   type Index is range 1 .. 10;
   type Element is new Integer;

   type Arr is array (Index) of Element;

   function Linear_Search
     (A        : Arr;
      Val      : Element;
      At_Index : out Index) return Boolean;
   --  Returns True if A contains value Val, in which case it also returns
   --  in At_Index the first index with value Val. Returns False otherwise.
end Search;
