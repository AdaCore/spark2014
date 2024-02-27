procedure Main with SPARK_Mode is
   type Nil is null record;
   type No is null record with Predicate => False;
   type No2 is record
      F : Nil;
      G : Nil;
      H : Nil;
   end record with Predicate => False;
   type Nil2 is record
      F : Nil;
      G : Nil;
   end record;
   type Nil3 is record
      F : Nil;
      G : Nil2;
   end record;
   type No3 is record
      F : Nil2;
      G : Nil3;
   end record with Predicate => False;
   type No4 is record
      F : No;
      G : Integer;
   end record;
   type No5 is record
      F : No2;
      G : Integer;
   end record;
   type No6 is record
      F : No3;
      G : Integer;
   end record;
   function Rand (I : Integer) return Integer
     with Import, Global => null;
begin
   case Rand (0) is
      when 0 =>
         declare
            X : array (1 .. 2) of No := (others => <>); --@PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
         begin
            null;
         end;
      when 1 =>
         declare
            X : array (2 .. 2) of No2 := (2 => <>); --@PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
         begin
            null;
         end;
      when 2 =>
         declare
            X : array (Rand (42) .. Rand (23)) of No3 :=
              (others => <>); --@PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
         begin
            null;
         end;
      when 3 =>
         declare
            X : No4 := (F => <>, G => 42); --@PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
         begin
            null;
         end;
      when 4 =>
         declare
            X : No5 := (F => <>, G => Rand (2)); --@PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
         begin
            null;
         end;
      when 5 =>
         declare
            X : No6 := (F => <>, G => Rand (7)); --@PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
         begin
            null;
         end;
      when others =>
         null;
   end case;
end Main;
