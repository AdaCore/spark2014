with Carver;

package body Carver_Test with
    SPARK_Mode => On
is

    type Integer_Array_Type is array (Natural range <>) of Integer;
    type Constant_Integer_Array_Ptr_Type is access constant Integer_Array_Type;
    package C is new Carver(Integer, Natural, Integer_Array_Type, Constant_Integer_Array_Ptr_Type);
    IA : aliased constant Integer_Array_Type := (1, 2);
    IAP : constant Constant_Integer_Array_Ptr_Type := IA'Access;

    procedure Execute is
        A : C.Carved_Array_Type;
    begin
        A := C.Make_Carved_Array(IAP);

        Ada.Text_IO.Put_Line(A.First'Image);
        Ada.Text_IO.Put_Line(A.Last'Image);
    end Execute;

end Carver_Test;
