with Ada.Text_IO;
package body Task_Types with SPARK_Mode is
   task body My_Task_Type is
      X : Natural := C;
   begin
      while True loop
         X := X + 1; --@OVERFLOW_CHECK:FAIL
      end loop;
   end My_Task_Type;

   procedure Do_Something (T1, T2 : My_Task_Type) is
      X : Natural := 0;
   begin
      if T1.C = T2.C then
         return;
      end if;
      while True loop
         X := X + 1; --@OVERFLOW_CHECK:FAIL
      end loop;
   end Do_Something;

   procedure Call is
   begin
      Do_Something (T, T2);
   end Call;
end Task_types;
