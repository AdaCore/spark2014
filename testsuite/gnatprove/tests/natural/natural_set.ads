package Natural_Set
  with SPARK_Mode
is
   ----------------------------------------------------
   --       SPARK 2014 - Natural_Set Example         --
   --                                                --
   -- This example illustrates a simple abstract     --
   -- data type for a bounded set of Naturals in     --
   -- SPARK 2014.                                    --
   --                                                --
   -- Note the use of expression functions in the    --
   -- private part of this package.                  --
   ----------------------------------------------------

   Maximum_Set_Size : constant Positive := 10;

   type T is private;

   function Valid (S : in T) return Boolean;

   function Members (S : in T) return Natural
     with Post => Members'Result >= 0 and
                  Members'Result <= Maximum_Set_Size;

   function Full (S : in T) return Boolean is (Members (S) = Maximum_Set_Size);

   procedure Create (S : out T)
     with Post => Valid (S) and
                  Members (S) = 0 and
                  not Full (S);

   function Contains (S     : in T;
                      Value : in Natural)
                      return Boolean;

   procedure Insert (S     : in out T;
                     Value : in     Natural)
     with Pre  => (Valid (S) and not Full (S)),
          Post => (Contains (S, Value));

private
   subtype Element_T is Integer range -1 .. Integer'Last;

   Invalid_Element : constant Element_T := Element_T'First;

   subtype Set_Length is Natural range 0 .. Maximum_Set_Size;
   subtype Set_Index is Set_Length range 1 .. Set_Length'Last;

   type Set_Array_T is array (Set_Index) of Element_T;

   type T is record
      Len : Set_Length;
      M   : Set_Array_T;
   end record;

   function Members (S : in T) return Natural is (S.Len);

   function Valid (S : in T) return Boolean is
     ((for all I in Set_Index range 1 .. S.Len => (S.M (I) in Natural)) and
        (for all I in Set_Index range S.Len + 1 .. Set_Index'Last =>
           (S.M (I) = Invalid_Element)));

   function Contains (S     : in T;
                      Value : in Natural)
                      return Boolean is
      (for some I in 1 .. S.Len => S.M (I) = Value);

end Natural_Set;
