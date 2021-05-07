package body UU
  with SPARK_Mode => On
is

   function C (Left, Right : in R) return Boolean
   is
   begin
      return Left = Right; --  @UU_RESTRICTION:FAIL
   end C;

   function C2 (Left, Right : in FR) return Boolean
   is
   begin
      return Left = Right; --  @UU_RESTRICTION:PASS
   end C2;

   function C3 (Left : in FR;
                Right : in R) return Boolean
   is
   begin
      return Left = Right; --  @UU_RESTRICTION:FAIL
   end C3;

   function C4 (Left, Right : in Holder) return Boolean
   is
   begin
      return Left = Right; --  @UU_RESTRICTION:FAIL
   end C4;

   function C5 (Left, Right : in Root1'Class) return Boolean
   is
   begin
      return Left = Right; --  @UU_RESTRICTION:FAIL
   end C5;

   function C6 (Left, Right : in Root2'Class) return Boolean
   is
   begin
      return Left = Right; --  @UU_RESTRICTION:NONE
   end C6;

   function C7 (Left, Right : in Holder2) return Boolean
   is
   begin
      return Left = Right; --  @UU_RESTRICTION:FAIL
   end C7;

   function C8 (Left, Right : in Holder3'Class) return Boolean
   is
   begin
      return Left = Right; --  @UU_RESTRICTION:FAIL
   end C8;

   function C9 (Left, Right : in Holder4) return Boolean
   is
   begin
      return Left = Right; --  @UU_RESTRICTION:NONE
   end C9;

   function C10 (Left, Right : in Holder5) return Boolean
   is
   begin
      return Left = Right; --  @UU_RESTRICTION:NONE
   end C10;

end UU;
