with System.Storage_Elements;

package Rich_Data
    with SPARK_Mode
is
    --  Specifying type representation in memory

    type Small_Int is range 0 .. 42
    with Alignment => 1, Size => 6, Object_Size => 8;

    type Rec is record
        A, B, C : Small_Int;
    end record
    with Size => 18, Pack;

    type Arr is array (Small_Int range 1 .. 3) of Small_Int
    with Size => 18, Pack;

    type Rec_With_Hole is record
        A, B, C : Small_Int;
    end record;
    for Rec_With_Hole use record
        A at 0 range 0 .. 5;
        B at 0 range 6 .. 11;
        C at 0 range 16 .. 21;
    end record;

    type Protocol is (Text, Binary);
    for Protocol use (Text => 42, Binary => 64);

    --  Contracts on types

    subtype Special_Small_Int is Small_Int
    with Predicate => Special_Small_Int in 0 | 5 .. 12 | 18 | 42;

    X : Special_Small_Int := 12;

    subtype Special_Rec is Rec
    with Predicate => Special_Rec.A < Special_Rec.B and Special_Rec.B < Special_Rec.C;

    Y : Special_Rec := (A => 10, B => 23, C => 42);

    subtype Special_Arr is Arr
    with Predicate => (for all I in Special_Arr'Range => Special_Arr(I) > 5 * I);

    Z : Special_Arr := (10, 23, 42);

end Rich_Data;
