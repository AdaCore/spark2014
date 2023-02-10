with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Maps.Higher_Order;

--  This test verifies the Higher_Order child package of functional maps. It
--  should remain all proved (except for flow checks linked to termination
--  right now, as we are waiting for improvements in this area).

procedure Test_Map_HO with SPARK_Mode is
   package Nested with
      Annotate => (GNATprove, Always_Return)
   is
      type Key_Type is private;
      type Element_Type is private;

      function Witness (K : Key_Type) return Big_Integer;
      function Witness (E : Element_Type) return Big_Integer;
      function Witness (W : Big_Integer) return Big_Integer;

      function "=" (Left, Right : Key_Type) return Boolean;
      function Equivalent_Keys
        (Left  : Key_Type;
         Right : Key_Type) return Boolean
      with
        Post => Equivalent_Keys'Result = (Witness (Left) = Witness (Right));
      function "=" (Left, Right : Element_Type) return Boolean with
        Post => "="'Result = (Witness (Left) = Witness (Right));
      function Equivalent_Elements
        (Left  : Element_Type;
         Right : Element_Type) return Boolean
      with
        Post => Equivalent_Elements'Result =
            (Witness (Witness (Left)) = Witness (Witness (Right)));

   private
      pragma SPARK_Mode (Off);

      type Key_Type is new Big_Integer;
      type Element_Type is new Big_Integer;

      function Witness (K : Key_Type) return Big_Integer is
        (Big_Integer (K));
      function Witness (E : Element_Type) return Big_Integer is
        (Big_Integer (E));
      function Witness (W : Big_Integer) return Big_Integer is
        (W);


      function "=" (Left, Right : Key_Type) return Boolean is
        (Witness (Left) = Witness (Right));
      function Equivalent_Keys
        (Left  : Key_Type;
         Right : Key_Type) return Boolean
      is (Left = Right);
      function "=" (Left, Right : Element_Type) return Boolean is
        (Witness (Left) = Witness (Right));
      function Equivalent_Elements
        (Left  : Element_Type;
         Right : Element_Type) return Boolean
      is (Left = Right);
   end Nested;
   use Nested;

   package My_Maps is new SPARK.Containers.Functional.Maps
     (Key_Type, Element_Type, Equivalent_Keys, "=", Equivalent_Elements);

   package HO is new My_Maps.Higher_Order;
begin
   null;
end Test_Map_HO;
