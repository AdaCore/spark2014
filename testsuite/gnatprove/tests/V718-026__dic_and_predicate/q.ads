with SPARK.Containers.Formal.Vectors;

package Q with SPARK_Mode is

    subtype Contained_Element is Character; -- for the moment

    package Element_Vectors is new SPARK.Containers.Formal.Vectors
      (Index_Type => Positive, Element_Type => Contained_Element);
    use Element_Vectors;

    subtype Set_Model is Vector (Contained_Element'Range_Length) with
      Predicate =>
         --  The Contained_Element values within a model are
         --  in strictly descending order. Hence they are also unique.
         (for all K in First_Index (Set_Model) .. Last_Index
(Set_Model) =>
                (if K /= Last_Index (Set_Model) then
                    Element (Set_Model, K) > Element (Set_Model, K + 1))),
      Ghost;

    function Model return Set_Model with Ghost;

end Q;
