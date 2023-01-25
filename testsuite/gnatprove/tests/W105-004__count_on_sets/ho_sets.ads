with SPARK.Big_Integers;     use SPARK.Big_Integers;
with SPARK.Containers.Functional.Sets;

package HO_Sets with SPARK_Mode is
   package My_Sets is new SPARK.Containers.Functional.Sets (Integer);
   use My_Sets;

   function Count
     (Container : Set;
      Test      : not null access function (Item : Integer) return Boolean)
      return Big_Integer
   with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Subprogram_Variant => (Decreases => Length (Container)),
     Annotate => (GNATprove, Always_Return),
     Post => Count'Result <= Length (Container);

   procedure Lemma_Count_Eq
     (Left, Right : Set;
      Test        : not null access function (Item : Integer) return Boolean)
   with Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Always_Return),
     Subprogram_Variant => (Decreases => Length (Left)),
     Pre  => Left = Right,
     Post => Count (Left, Test) = Count (Right, Test);

   procedure Lemma_Count_Remove
     (Container : Set;
      Item      : Integer;
      Test      : not null access function (Item : Integer) return Boolean)
   with Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Always_Return),
     Subprogram_Variant => (Decreases => Length (Container) - 1),
     Pre  => Contains (Container, Item),
     Post => Count (Container, Test) =
         Count (Remove (Container, Item), Test) +
           (if Test (Item) then Big_Integer'(1) else Big_Integer'(0));

end HO_Sets;
