with SPARK.Big_Integers;
with SPARK.Big_Intervals;
with SPARK.Containers.Functional.Infinite_Sequences;

procedure AvI_Infinite_Sequences with SPARK_Mode is
    use type SPARK.Big_Integers.Big_Integer;
    type Subelement_Type is range 0 .. (2**64 - 1);
    type Element_Type is record
        x, y : Subelement_Type := 0;
    end record with Predicate =>
        (if y > 0 then y - 1 <= Subelement_Type'Last - x);
    type Node_Type;
    type Node_Ptr_Type is access Node_Type;
    type Node_Type is record
        Value : Element_Type;
        Next : aliased Node_Ptr_Type;
    end record;

    subtype Positive_Index_Type is SPARK.Big_Integers.Big_Positive;
    subtype Natural_Index_Type is SPARK.Big_Integers.Big_Natural;
    package Seq is new SPARK.Containers.Functional.Infinite_Sequences(Element_Type);
    subtype Array_Type is Seq.Sequence;



    Empty_Array : constant Array_Type := Seq.Empty_Sequence;
    function Prepend(V : Element_Type; A : Array_Type) return Array_Type is (Seq.Add(A, 1, V));


    function Last(A : Array_Type) return Natural_Index_Type is (Seq.Last(A));
    function Length(A : Array_Type) return Natural_Index_Type is (Last(A));
    function Get(A : Array_Type; I : Positive_Index_Type) return Element_Type is (Seq.Get(A, I))
    with Pre => I <= Length(A);

    function At_End(Node : access constant Node_Type) return access constant Node_Type is (Node)
    with
        Ghost,
        Global => null,
        Annotate => (GNATprove, At_End_Borrow);

    function Model(Node : access constant Node_Type) return Array_Type is (
        if Node = null then (
            Empty_Array
        ) else (
            Prepend(Node.Value, Model(Node.Next))
        )
    ) with
        Ghost,
        Subprogram_Variant => (Structural => Node);

    procedure Find_And_Modify(Node : aliased in out Node_Ptr_Type) is
        Orig_Model : constant Array_Type := Model(Node) with Ghost;
        Cursor : not null access Node_Ptr_Type := Node'Access;
        Index : Natural_Index_Type := 0;
    begin
        while Cursor.all /= null loop
            pragma Loop_Invariant(0 <= Index and then Index <= Last(Orig_Model));
            pragma Loop_Invariant(Length(Model (At_End (Node))) =
                Index + Length(Model(At_End(Cursor.all))));
            pragma Loop_Invariant(Length(Orig_Model) = Index + Length(Model(Cursor.all)));
            pragma Loop_Invariant(for all I in SPARK.Big_Intervals.Interval'(1, Index) =>
                Get(Model(At_End(Node)), I) = Get(Orig_Model, I));
            pragma Loop_Invariant(for all I in
                SPARK.Big_Intervals.Interval'(Index + 1, Last(Model(At_End(Node)))) =>
                    Get(Model(At_End(Node)), I) = Get(Model(At_End(Cursor.all)), I - Index));
            pragma Loop_Invariant(for all I in
                SPARK.Big_Intervals.Interval'(Index + 1, Last(Orig_Model)) =>
                    Get(Orig_Model, I) = Get(Model(Cursor.all), I - Index));

            Cursor := Cursor.all.Next'Access;
            Index := Index + 1;
        end loop;
    end Find_And_Modify;
begin
   null;
end AvI_Infinite_Sequences;
