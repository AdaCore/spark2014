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
     Annotate => (GNATprove, Container_Aggregates, "Model"), Import;

   procedure Include (S : in out Set_Type; N : in Integer);
private
   type Set_Type is new Integer;
end;
