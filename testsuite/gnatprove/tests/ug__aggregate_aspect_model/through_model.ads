with SPARK.Containers.Functional.Infinite_Sequences;

package Through_Model with SPARK_Mode is
   package My_Seqs is new SPARK.Containers.Functional.Infinite_Sequences (Integer);
   use My_Seqs;

   type List is private with
     Aggregate => (Empty => Empty_List, Add_Unnamed => Add),
     Annotate  => (GNATprove, Container_Aggregates, "From_Model");

   Empty_List : constant List;

   function Model (L : List) return Sequence with
     Subprogram_Variant => (Structural => L),
     Annotate => (GNATprove, Container_Aggregates, "Model");

   procedure Add (L : in out List; E : Integer) with
     Always_Terminates,
     Post => Model (L) = Add (Model (L)'Old, E);

private

   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : Integer;
      Next : List;
   end record;

   function Model (L : List) return Sequence is
     (if L = null then Empty_Sequence
      else Add (Model (L.Next), L.Data));

   Empty_List : constant List := null;
end Through_Model;
