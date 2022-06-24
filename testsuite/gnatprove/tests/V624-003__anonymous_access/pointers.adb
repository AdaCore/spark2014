package body Pointers
    with SPARK_Mode => On
is

    procedure Move_Ptrs (Out_Arr : Out Object_Ptr_Arr) is
    begin
        for I in Object_Ptr_Arr'Range loop
            Out_Arr(I) := Global_Arr(I)'Access;
        end loop;
    end Move_Ptrs;

end Pointers;
