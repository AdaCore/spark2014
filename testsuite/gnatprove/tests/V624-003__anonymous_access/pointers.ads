package Pointers
    with SPARK_Mode => On
is
    type Object is new Integer;
    type Object_Arr is array (1..4) of aliased Object;
    type Object_Ptr_Arr is array (1..4) of access constant Object;

    type Object_Rec is record
       Comp : access Object;
    end record;

    Global_Arr : Object_Arr := (1,2,3,4);

    procedure Move_Ptrs (Out_Arr : Out Object_Ptr_Arr);
end Pointers;
