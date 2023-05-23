with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Infinite_Sequences.Higher_Order;

--  This test verifies the Higher_Order child package of infinite sequences. It
--  should remain all proved (except for flow checks linked to termination
--  right now, as we are waiting for improvements in this area).

procedure Test_Sequence_HO with SPARK_Mode is
   package Nested with
      Annotate => (GNATprove, Always_Return)
   is
      type Element_Type is private;

      function Witness (E : Element_Type) return Big_Integer;
      function Witness (W : Big_Integer) return Big_Integer;

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
      type Element_Type is new Big_Integer;
      function Witness (E : Element_Type) return Big_Integer is
        (Big_Integer (E));
      function Witness (W : Big_Integer) return Big_Integer is
        (W);

      function "=" (Left, Right : Element_Type) return Boolean is
        (Witness (Left) = Witness (Right));
      function Equivalent_Elements
        (Left  : Element_Type;
         Right : Element_Type) return Boolean
      is (Left = Right);
   end Nested;
   use Nested;

   package My_Sequences is new SPARK.Containers.Functional.Infinite_Sequences
     (Element_Type,  "=", Equivalent_Elements);

   package HO is new My_Sequences.Higher_Order;
begin
   null;
end Test_Sequence_HO;
