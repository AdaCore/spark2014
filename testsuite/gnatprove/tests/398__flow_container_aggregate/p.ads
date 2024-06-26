with SPARK.Containers.Functional.Infinite_Sequences;

package P is
   package My_Seqs is
     new SPARK.Containers.Functional.Infinite_Sequences (Integer);
   use My_Seqs;

   type Set_Type is private
     with Aggregate => (Empty       => Empty_Set,
                        Add_Unnamed => Include),
          Annotate => (GNATprove, Container_Aggregates, "From_Model");

   function Empty_Set return Set_Type;

   function Model (S : Set_Type) return Sequence with
     Post => (if Model'Result = Empty_Sequence then S = P.Empty_Set),
     Annotate => (GNATprove, Container_Aggregates, "Model");

   procedure Include (S : in out Set_Type; N : in Integer)
      with Pre => N = 0, Always_Terminates;

private
   type Set_Type is record
      C : Integer;
   end record;
end;
