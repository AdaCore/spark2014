procedure Main with SPARK_Mode is
   type U64 is mod 2 ** 64;
   type A is array (U64 range <>) of U64;
   procedure Test64 (X : in out A);
   procedure Test64 (X : in out A) is
      Y : constant U64 := X'Length; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test64;

   type U8 is mod 2 ** 8;
   type B is array (U8 range <>) of U64;
   function Make (X : U8) return B is (0 .. X => 42);
   procedure Test8 with Global => null;
   procedure Test8 is
      V0 : constant U8 := Make (255)'Length; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test8;

   type U16 is mod 2 ** 16;
   function Rand return U16 with Global => null, Import;
   type C is array (U16 range 0 .. Rand) of U64;
   procedure Test16 with Global => null;
   procedure Test16 is
      V1 : constant U16 := C'Length; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test16;

begin
   null;
end Main;
