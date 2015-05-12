
----------------------------------------------------
-- SPARK 2014 - Linear Search Example             --
--                                                --
-- This example illustrates the use of Pre, Post  --
-- and Contract_Cases aspects in SPARK 2014.      --
----------------------------------------------------

package Linear_Search
  with SPARK_Mode
is

   type Index is range 1 .. 10;
   type Element is new Integer;

   type Arr is array (Index) of Element;

   type Search_Result (Found : Boolean := False) is record
      case Found is
         when True =>
            At_Index : Index;
         when False =>
            null;
      end case;
   end record;

   function Value_Found_In_Range
     (A       : Arr;
      Val     : Element;
      Low, Up : Index) return Boolean
   is (for some J in Low .. Up => A(J) = Val);

   function Search
     (A   : Arr;
      Val : Element) return Search_Result
   with
     Pre  => Val >= 0,
     Post => (if Search'Result.Found then
                A (Search'Result.At_Index) = Val),
     Contract_Cases =>
       (A(1) = Val =>
          Search'Result.At_Index = 1,
        A(1) /= Val and then Value_Found_In_Range (A, Val, 2, 10) =>
          Search'Result.Found,
        (for all J in Arr'Range => A(J) /= Val) =>
          not Search'Result.Found);

end Linear_Search;
