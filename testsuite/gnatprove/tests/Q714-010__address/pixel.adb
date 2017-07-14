with System.Storage_Elements; use System.Storage_Elements;

procedure Pixel with SPARK_Mode is

   Buffer : constant System.Address := System'To_Address (0);

   function Zero return Natural is (0);

   procedure Aspect with
      Import, Address => Buffer + (Buffer mod Storage_Offset (1 / Zero));

   procedure Clause with
      Import;
   for Clause'Address use Buffer + (Buffer mod Storage_Offset (1 / Zero));

begin
   Aspect;
   Clause;
end Pixel;
