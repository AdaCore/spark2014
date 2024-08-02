with SPARK.Containers.Functional.Vectors;
with Interfaces; use Interfaces;

package P is
   subtype Base_8 is Integer range 1 .. 7;
   package My_Seqs is
     new SPARK.Containers.Functional.Vectors (Base_8, Boolean);
   use My_Seqs;

   type Seq_Type is private
     with Aggregate => (Empty       => Empty_Seq,
                        Add_Unnamed => Include),
          Annotate => (GNATprove, Container_Aggregates, "From_Model");

   function Empty_Seq return Seq_Type;

   function Is_Model (S : Seq_Type; M : Sequence) return Boolean;

   function Model (S : Seq_Type) return Sequence with
     Annotate => (GNATprove, Container_Aggregates, "Model"),
     Post => Is_Model (S, Model'Result);

   procedure Include (S : in out Seq_Type; B : Boolean) with Always_Terminates,
     Pre => Last (Model (S)) < 7,
     Post => Model (S) = Add (Model (S)'Old, B);
private
   type Seq_Type is new Interfaces.Unsigned_8 with Predicate => Seq_Type /= 0;

   function Is_Model (S : Seq_Type; M : My_Seqs.Sequence) return Boolean is
     (Last (M) =
      (if S < 2 then 0
       elsif S < 4 then 1
       elsif S < 8 then 2
       elsif S < 16 then 3
       elsif S < 32 then 4
       elsif S < 64 then 5
       elsif S < 128 then 6
       else 7)
      and then (for all I in 1 .. Last (M) =>
           Get (M, I) = (Shift_Right (S, Last (M) - I) mod 2 = 1)));
end;
