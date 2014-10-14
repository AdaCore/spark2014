package Skp
is

   type CPU_Range is range 0 .. 3;

   subtype Subject_Id_Type is Natural range 0 .. 6;

   Invalid_Subject : constant := Subject_Id_Type'Last + 1;

   subtype Dst_Subject_Type is Natural range 0 .. Invalid_Subject;

   type Vector_Range is range 0 .. 255;

   Invalid_Vector : constant := 256;

   type Dst_Vector_Range is range 0 .. Invalid_Vector;

   Vmxon_Address : constant := 16#1000#;

end Skp;
