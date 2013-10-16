pragma SPARK_Mode;

package Search is

   type Index is range 1 .. 10;
   type Element is new Integer;

   type Arr is array (Index) of Element;

   type Search_Result is record
      Found    : Boolean;
      At_Index : Index;
   end record;

   function Linear_Search
     (A   : Arr;
      Val : Element) return Search_Result;

end Search;
