procedure Test_Callback with SPARK_Mode is
   type Incr_Fun is not null access function
     (X : Integer) return Integer
   with Pre => X < 100,
     Post => Incr_Fun'Result >= X;
   type Strict_Incr_Fun is not null access function
     (X : Integer) return Integer
   with Pre => X + 1 < 100, --@OVERFLOW_CHECK:FAIL
     Post => Strict_Incr_Fun'Result > X;
   subtype S is Incr_Fun with
     Predicate => S (1) = 2;
   type Incr_Fun_2 is access function
     (X : Integer) return Integer
   with Pre => X < 50;

   type Rec is record
      X : Strict_Incr_Fun;
   end record;

   procedure Junk is
   begin
      null;
   end Junk;

   function Increment (X : Integer) return Integer is (X + 1) with
     Pre => X < Integer'Last;

   function Increment_2 (X : Integer) return Integer with
     Import,
     Pre => X < Integer'Last;

   function Call_Incr_Fun (F : Incr_Fun; G : Incr_Fun; X : Integer) return Integer with
     Pre => X < 100,
     Post => Call_Incr_Fun'Result >= X
   is
   begin
      return Incr_Fun'(if X > 0 then F else G).all (X);
   end Call_Incr_Fun;

   function Call_Incr_Bad (F : Incr_Fun; X : Integer) return Integer with
     Pre => X <= 100,
     Post => Call_Incr_Bad'Result > X --@POSTCONDITION:FAIL
   is
   begin
      return F (X); --@PRECONDITION:FAIL
   end Call_Incr_Bad;

   function Call_Incr_Bad2 (F : Incr_Fun_2; X : Integer) return Integer with
     Pre => X < 100,
     Post => Call_Incr_Bad2'Result >= X
   is
   begin
      return F (X); --@DEREFERENCE_CHECK:FAIL
   end Call_Incr_Bad2;

   function Call_Incr_Fun_Conv (F : Incr_Fun; X : Integer) return Integer with
     Pre => X < 50,
     Post => Call_Incr_Fun_Conv'Result >= X
   is
   begin
      return Incr_Fun_2 (F).all (X);
   end Call_Incr_Fun_Conv;

   function Call_Incr_Fun_Conv_Bad (F : Incr_Fun; X : Integer) return Integer with
     Pre => X < 100,
     Post => Call_Incr_Fun_Conv_Bad'Result >= X
   is
   begin
      return Incr_Fun_2 (F).all (X); --@PRECONDITION:FAIL
   end Call_Incr_Fun_Conv_Bad;

   function Call_Incr_Fun_Conv_Bad2 (F : Incr_Fun_2; X : Integer) return Integer with
     Pre => F /= null and then X < 50
   is
   begin
      return Incr_Fun (F).all (X); --@WEAKER_PRE_ACCESS:FAIL @STRONGER_POST_ACCESS:FAIL
   end Call_Incr_Fun_Conv_Bad2;

   type Null_Proc is not null access procedure with
     Pre => False;

   procedure Call_Null_Proc (P : Null_Proc) with
     Pre => True
   is
   begin
      P.all; --@PRECONDITION:FAIL
   end Call_Null_Proc;

   function Choose (F : access function (X : Integer) return Integer;
                    G : access function (X : Integer) return Integer;
                    B : Boolean) return access function (X : Integer) return Integer is
     (if B then F else G);

   function Choose_2 (F : access function (X : Integer) return Integer;
                      G : Incr_Fun;
                      B : Boolean) return Incr_Fun_2 is
     (if B then F else Incr_Fun_2 (G));

   function Choose_3 (F : Incr_Fun;
                      G : Incr_Fun;
                      B : Boolean) return Incr_Fun is
     (if B then F else Incr_Fun (G));

   procedure P (X : Integer; F : out S) with
     Pre => X < 100,
     Post => F (X) = X + 1
   is
   begin
      F := Increment'Access;
   end P;

   X : Incr_Fun := Increment'Access;
   Y : access function (X : Integer) return Integer := Increment_2'Access; --@WEAKER_PRE_ACCESS:FAIL
   Z : Incr_Fun := Increment_2'Access; --@STRONGER_POST_ACCESS:FAIL
begin
   pragma Assert (Incr_Fun_2 (X) = Choose_2 (Y, Increment'Access, False));
   pragma Assert (X in S);
   pragma Assert (Y in S); --@ASSERT:FAIL
end Test_Callback;
