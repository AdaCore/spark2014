pragma Restrictions(No_Secondary_Stack);

generic

    type Element_Type is private;
    type Element_Index_Type is (<>);
    type Array_Type is array (Element_Index_Type range <>) of Element_Type;
    type Constant_Array_Ptr_Type is access constant Array_Type;
--    with function "="(A, B : Element_Type) return Boolean;

package Carver is

    type Raw_Carved_Array_Type(
        First : Element_Index_Type := Element_Index_Type'Last;
        Last : Element_Index_Type := Element_Index_Type'First) is
    record
        Data : Constant_Array_Ptr_Type(First .. Last) := null;
    end record;

    subtype Carved_Array_Type is Raw_Carved_Array_Type with
        Dynamic_Predicate =>
            (Carved_Array_Type.First <= Carved_Array_Type.Last) = (Carved_Array_Type.Data /= null);

    function Make_Carved_Array(A : not null Constant_Array_Ptr_Type) return Carved_Array_Type is
        (Carved_Array_Type'(First => A'First, Last => A'Last, Data => A))
    with
        Pre => A'Last in Element_Index_Type and A'Length > 0;

    function Make_Carved_Array return Carved_Array_Type is
        (Carved_Array_Type'(
            First => Element_Index_Type'Last,
            Last => Element_Index_Type'First,
            Data => null));

end Carver;
