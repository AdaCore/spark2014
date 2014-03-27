-- Martin Brain
-- martin.brain@altran-praxis.com
-- 17/08/11
--
-- Examples of common array algorithms.
--
-- These are taken from "ACSL By Example" from Fraunhofer First:
--
-- http://www.first.fraunhofer.de/fileadmin/FIRST/ACSL-by-Example.pdf
--
-- And are originally derived from the C++ STL algortihms

package Array_Algorithms
is

   type Value_Type    is new Integer;
   type Index_Type    is new Integer;
   type Generic_Array is array (Index_Type range <>) of Value_Type;

   function Equal (A, B : Generic_Array) return Boolean is
     (for all I in Index_Type range A'First .. A'Last => A (I) = B (I))
     with Pre  => A'First = B'First and A'Last = B'Last;


   procedure Mismatch (A, B     : in     Generic_Array;
                       Found    :    out Boolean;
                       Location :    out Index_Type)
     with Depends => ((Found, Location) => (A, B)),
          Pre     => A'First = B'First and A'Last = B'Last,
          Post    =>
            (if Found then Location in A'Range
                             and A (Location) /= B (Location)
                             and (for all I in Index_Type range
                                        A'First..Location - 1 => A (I) = B (I))
             else (for all I in Index_Type range
                     A'First..A'Last => A (I) = B (I)));


   function Has_Value_Inc (A         : in Generic_Array;
                           LastIndex : in Index_Type;
                           Val       : in Value_Type)
                          return Boolean
   is (for some I in Index_Type range A'First..LastIndex => A (I) = Val)
     with Pre => LastIndex in A'Range;


   function Has_Value_Exc (A         : in Generic_Array;
                           LastIndex : in Index_Type;
                           Val       : in Value_Type)
                          return Boolean
   is (for some I in Index_Type range A'First..LastIndex =>
         I < LastIndex and A (I) = Val)
     with Pre => LastIndex in A'Range;


   procedure Find (A        : in     Generic_Array;
                   Val      : in     Value_Type;
                   Found    :    out Boolean;
                   Location :    out Index_Type)
     with Depends => ((Found, Location) => (A, Val)),
          Post    => (if Found then Location in A'Range
                                      and A (Location) = Val
                                      and Has_Value_Inc (A, A'Last, Val)
                                      and not Has_Value_Exc (A, Location, Val)
                      else not Has_Value_Inc (A, A'Last, Val));

end Array_Algorithms;
