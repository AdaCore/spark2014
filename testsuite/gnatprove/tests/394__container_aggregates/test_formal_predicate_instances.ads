with SPARK.Containers.Types; use SPARK.Containers.Types;
with SPARK.Containers.Formal.Doubly_Linked_Lists;
with SPARK.Containers.Formal.Hashed_Maps;
with SPARK.Containers.Formal.Hashed_Sets;
with SPARK.Containers.Formal.Ordered_Maps;
with SPARK.Containers.Formal.Ordered_Sets;
with SPARK.Containers.Formal.Vectors;

package Test_Formal_Predicate_Instances is

   subtype Index_Type is Positive;
   subtype Key_Type is Positive;
   type Rec is record Value : Integer; end record;
   subtype Element_Type is Rec with Predicate => Element_Type.Value > 0;
   function R (Val : Integer) return Rec is (Rec'(Value => Val));

   package Nested is
      function Hash (X : Key_Type) return Hash_Type is
        (Hash_Type (X))
      with Global => null;

      function Hash (X : Element_Type) return Hash_Type is
        (Hash_Type (X.Value))
      with Global => null;

      function "<" (X, Y : Element_Type) return Boolean is (X.Value < Y.Value);
   end Nested;
   use Nested;

   function Get_Value return Integer
     with Import, Global => null;

   package My_Lists is new SPARK.Containers.Formal.Doubly_Linked_Lists (Element_Type);

   package My_HMaps is new SPARK.Containers.Formal.Hashed_Maps (Key_Type, Element_Type, Hash);

   package My_HSets is new SPARK.Containers.Formal.Hashed_Sets (Element_Type, Hash);

   package My_OMaps is new SPARK.Containers.Formal.Ordered_Maps (Key_Type, Element_Type);

   package My_OSets is new SPARK.Containers.Formal.Ordered_Sets (Element_Type);

   package My_Vectors is new SPARK.Containers.Formal.Vectors (Index_Type, Element_Type);

end;
