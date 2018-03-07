with System.Storage_Elements; use System.Storage_Elements;

procedure Pixel with SPARK_Mode is

   Buffer : constant System.Address := System'To_Address (0);

   function Zero return Natural is (0);

   procedure Aspect with
      Import, Address => Buffer + (Buffer mod Storage_Offset (1 / Zero)); --@DIVISION_CHECK:FAIL

   procedure Clause with
      Import;
   for Clause'Address use Buffer + (Buffer mod Storage_Offset (1 / Zero)); --@DIVISION_CHECK:FAIL

   Asp : Integer with
      Import, Address => Buffer + (Buffer mod Storage_Offset (1 / Zero)); --@DIVISION_CHECK:FAIL

   Cla : Integer with
      Import;
   for Cla'Address use Buffer + (Buffer mod Storage_Offset (1 / Zero)); --@DIVISION_CHECK:FAIL

begin
   Aspect;
   Clause;
end Pixel;
