with SPARK.Containers.Functional.Infinite_Sequences;

procedure Basic
  with SPARK_Mode
is
   package Memory_Index_Sequences is new
     SPARK.Containers.Functional.Infinite_Sequences (Positive);
   use Memory_Index_Sequences;

   type Set_Model is record
      Buckets : Sequence;
   end record
   with
     Predicate =>
       (for all I of Buckets => True);

begin
   null;
end;
