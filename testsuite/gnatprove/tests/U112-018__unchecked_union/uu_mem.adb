package body UU_mem
  with SPARK_Mode => On
is

   function C (Left, Right : in R) return Boolean
   is
   begin
      return Left in Right | R; --  @UU_RESTRICTION:FAIL
   end C;

   function C2 (Left, Right : in FR) return Boolean
   is
   begin
      return Left in Right | FR; --  @UU_RESTRICTION:PASS
   end C2;

   function C3 (Left : in FR;
                Right : in R) return Boolean
   is
   begin
      return Left in Right | FR; --  @UU_RESTRICTION:FAIL
   end C3;

   function C4 (Left, Right : in Holder) return Boolean
   is
   begin
      return Left in Right | Holder; --  @UU_RESTRICTION:FAIL
   end C4;

   function C5 (Left, Right : in Root1'Class) return Boolean
   is
   begin
      return Left in Right | Root1'Class; --  @UU_RESTRICTION:FAIL
   end C5;

   function C6 (Left, Right : in Root2'Class) return Boolean
   is
   begin
      return Left in Right | Child2'Class; --  @UU_RESTRICTION:NONE
   end C6;

   function C7 (Left : in FR;
                Right : in R) return Boolean
   is
   begin
      return Left in FR --  @UU_RESTRICTION:PASS
        and then Right in FR; --  @UU_RESTRICTION:FAIL
   end C7;

   function C8 (Left : in FR;
                Right : in R) return Boolean
   is
   begin
      return Left in R --  @UU_RESTRICTION:PASS
        and then Right in R; --  @UU_RESTRICTION:PASS
   end C8;

end UU_mem;
