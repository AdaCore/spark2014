procedure Main with SPARK_Mode is

   type My_Int is new Integer with Relaxed_Initialization;

   Overflow : exception;

   procedure Incr (Y : My_Int; X : aliased out My_Int) with
     Post => X = Y + 1 and Y < My_Int'Last,
     Exceptional_Cases => (Overflow => Y = My_Int'Last and then X'Initialized and then X = Y);

   procedure Incr (Y : My_Int; X : aliased out My_Int) is
   begin
      X := Y;
      if X = My_Int'Last then
         raise Overflow;
      else
         X := X + 1;
      end if;
   end Incr;

   procedure Bad_Incr (Y : My_Int; X : aliased out My_Int) with
     Post => X = Y + 1,
     Exceptional_Cases => (Overflow => Y = My_Int'Last);

   procedure Bad_Incr (Y : My_Int; X : aliased out My_Int) is
   begin
      if Y = My_Int'Last then
         raise Overflow;
      else
         X := Y + 1;
      end if;
   end Bad_Incr;

   procedure Incr_Twice (Y : My_Int; X : aliased out My_Int) with
     Post => X = Y + 2,
     Exceptional_Cases => (Overflow => Y >= My_Int'Last - 1 and then X = My_Int'Last);

   procedure Incr_Twice (Y : My_Int; X : aliased out My_Int) is
   begin
      X := Y;
      Incr (X, X);
      Incr (X, X);
   end Incr_Twice;

   procedure Bad_Incr_Twice (Y : My_Int; X : aliased out My_Int) with
     Post => X = Y + 2,
     Exceptional_Cases => (Overflow => Y >= My_Int'Last - 1 and then X = My_Int'Last);  --@INIT_BY_PROOF:FAIL

   procedure Bad_Incr_Twice (Y : My_Int; X : aliased out My_Int) is
   begin
      X := Y;
      Bad_Incr (X, X);
      Bad_Incr (X, X);
   end Bad_Incr_Twice;

   package Nested is
      type Priv is private with Relaxed_Initialization;

      function Get (X : Priv) return Integer;

      procedure Incr (Y : Integer; X : out Priv) with
        Post => Get (X) = Y + 1,
        Exceptional_Cases => (Overflow => Y = Integer'Last);
   private
      pragma SPARK_Mode (Off);
      type Priv is record
         I : Integer;
         J : Integer;
      end record;
   end Nested;

   package body Nested with SPARK_Mode => Off is

      function Get (X : Priv) return Integer is (X.I);

      procedure Incr (Y : Integer; X : out Priv) is
      begin
         if Y = Integer'Last then
            raise Overflow;
         else
            X.I := Y + 1;
         end if;
      end Incr;
   end Nested;
   use Nested;

   procedure Incr_Twice (Y : Integer; X : out Priv) with
     Post => Get (X) = Y + 2,
     Exceptional_Cases => (Overflow => Y >= Integer'Last - 1);

   procedure Incr_Twice (Y : Integer; X : out Priv) is
   begin
      Incr (Y, X);
      Incr (Get (X), X);
   end Incr_Twice;

begin
   null;
end Main;
