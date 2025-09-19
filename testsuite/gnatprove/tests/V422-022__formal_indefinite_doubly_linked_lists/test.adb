with SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists;

procedure Test with SPARK_Mode is
   package Lists is new SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists
     (String);
   use Lists;

   L : List;

begin
   Append (L, "A");
   Append (L, "B");
   Append (L, "C");

   pragma Assert (Element (L, Last (L)) = "C");

end Test;
