

package Search is 

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

   function Linear_Search
     (A   : Arr;
      Val : Element) return Search_Result
   with
     Pre  => Val >= 0,
     Post => (if Linear_Search'Result.Found then
                A (Linear_Search'Result.At_Index) = Val),
     Contract_Cases =>
       (A(1) = Val =>
          Linear_Search'Result.At_Index = 1,
        A(1) /= Val and then Value_Found_In_Range (A, Val, 2, 10) =>
          Linear_Search'Result.Found,
        (for all J in Arr'Range => A(J) /= Val) =>
          not Linear_Search'Result.Found);

end Search;
