with Ada.Unchecked_Conversion;

procedure Null_Record_Target with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Bytes is array (1 .. 0) of Byte
     with Component_Size => 8, Size => 0;
   type Empty is null record with Size => 0;
   type Derived_Empty is new Empty with Size => 0;

   function To_Empty is new Ada.Unchecked_Conversion (Bytes, Empty);
   function To_Derived is new Ada.Unchecked_Conversion (Bytes, Derived_Empty);

   X : constant Bytes := (others => 0);
   Y : constant Empty := To_Empty (X);
   Z : constant Derived_Empty := To_Derived (X);
begin
   pragma Assert (Y = (null record));
   pragma Assert (Z = (null record));
end Null_Record_Target;
