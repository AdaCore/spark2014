pragma Restrictions(No_Secondary_Stack);

generic

    type Element_Type is private;
    type Element_Index_Type is (<>);
    type Array_Type is array (Element_Index_Type range <>) of Element_Type;
    type Constant_Array_Ptr_Type is not null access constant Array_Type;

package Carver is

    type Carved_Array_Type(
        First : Element_Index_Type'Base := Element_Index_Type'Last;
        Last : Element_Index_Type'Base := Element_Index_Type'First) is
    record
        Data : Constant_Array_Ptr_Type(First .. Last);
    end record;

    function Make_Carved_Array(A : Constant_Array_Ptr_Type) return Carved_Array_Type is
        (Carved_Array_Type'(First => A'First, Last => A'Last, Data => A));

    function Make_Carved_Array return Carved_Array_Type is
        (Carved_Array_Type'(First => Element_Index_Type'Last,
            Last => Element_Index_Type'First, Data => null));

end Carver;
