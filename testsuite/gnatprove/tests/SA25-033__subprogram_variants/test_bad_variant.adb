with Interfaces;

procedure Test_Bad_Variant with SPARK_Mode is

   function Bad_1 (X : Natural) return Boolean with
     Pre => X = 0 or else Bad_1 (X - 1), --@SUBPROGRAM_VARIANT:FAIL
     Subprogram_Variant => (Decreases => X),
     Import;

   function Bad_2 (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => X),
     Post => (if X = 0 then Bad_2'Result);

   type T is record
      X : Natural;
   end record;
   subtype S is T with
     Predicate => Bad_2 (S.X);

   function Bad_2 (X : Natural) return Boolean is
      L : T := (X => 0);
   begin
      if X = 0 then
         return True;
      end if;
      return L in S; --  Indirect recursive call not detected currently in proof
   end Bad_2;

   function Bad_3 (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => X);

   function Bad_3 (X : Natural) return Boolean is
   begin
      if X = 0 then
         return True;
      end if;

      declare
         package Nested is
            B : constant Boolean := Bad_3 (X - 1); --@SUBPROGRAM_VARIANT:FAIL
         end Nested;
      begin
         return Nested.B;
      end;
   end Bad_3;

   function Ok (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => X);

   function Ok (X : Natural) return Boolean is
      package Nested is
         B : constant Boolean := (if X = 0 then True else Ok (X - 1)); --@SUBPROGRAM_VARIANT:PASS
      end Nested;
   begin
      if X = 0 then
         return True;
      end if;
      return Nested.B;
   end Ok;

   function Even (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => X);

   function Odd (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => X);

   function Even (X : Natural) return Boolean is
   begin
      if X = 0 then
         return True;
      else
         return Odd (X - 1); --@SUBPROGRAM_VARIANT:PASS
      end if;
   end Even;

   function Odd (X : Natural) return Boolean is
   begin
      if X = 0 then
         return False;
      else
         return Even (X - 1); --@SUBPROGRAM_VARIANT:PASS
      end if;
   end Odd;

   function Even_Bad (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => X);

   function Odd_Bad (X : Natural) return Boolean with
     Subprogram_Variant => (Increases => - X);

   function Even_Bad (X : Natural) return Boolean is
   begin
      if X = 0 then
         return True;
      else
         return Odd_Bad (X - 1); --@SUBPROGRAM_VARIANT:FAIL
      end if;
   end Even_Bad;

   function Odd_Bad (X : Natural) return Boolean is
   begin
      if X = 0 then
         return False;
      else
         return Even_Bad (X - 1); --@SUBPROGRAM_VARIANT:FAIL
      end if;
   end Odd_Bad;

   function Even_Bad_2 (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => X);

   function Odd_Bad_2 (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => - X);

   function Even_Bad_2 (X : Natural) return Boolean is
   begin
      if X = 0 then
         return True;
      else
         return Odd_Bad_2 (X - 1); --@SUBPROGRAM_VARIANT:PASS
      end if;
   end Even_Bad_2;

   function Odd_Bad_2 (X : Natural) return Boolean is
   begin
      if X = 0 then
         return False;
      else
         return Even_Bad_2 (X - 1); --@SUBPROGRAM_VARIANT:FAIL
      end if;
   end Odd_Bad_2;

   function Even_Bad_3 (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => X);

   function Odd_Bad_3 (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => Interfaces.Unsigned_64 (X));

   function Even_Bad_3 (X : Natural) return Boolean is
   begin
      if X = 0 then
         return True;
      else
         return Odd_Bad_3 (X - 1); --@SUBPROGRAM_VARIANT:FAIL
      end if;
   end Even_Bad_3;

   function Odd_Bad_3 (X : Natural) return Boolean is
   begin
      if X = 0 then
         return False;
      else
         return Even_Bad_3 (X - 1); --@SUBPROGRAM_VARIANT:FAIL
      end if;
   end Odd_Bad_3;

   function Infinite (X : Integer) return Boolean is
     (Infinite (- X)) --@SUBPROGRAM_VARIANT:FAIL
   with Pre => X /= Integer'First,
     Subprogram_Variant => (Decreases => X, Increases => - X);--@OVERFLOW_CHECK:PASS

   function Bad_4 (X, Y : Integer; B : Boolean) return Boolean is
     (if B then Bad_4 (X + 1, Y - 6, B) --@SUBPROGRAM_VARIANT:FAIL @OVERFLOW_CHECK:FAIL
      else Bad_4 (X, Y + 1, B)) --@SUBPROGRAM_VARIANT:PASS @OVERFLOW_CHECK:FAIL
   with Subprogram_Variant => (Increases => Y, Increases => X);

   function OK_2 (X, Y : Integer; B : Boolean) return Boolean is
     (if B then OK_2 (X + 1, Y - 6, B) --@SUBPROGRAM_VARIANT:PASS @OVERFLOW_CHECK:FAIL
      else OK_2 (X, Y + 1, B)) --@SUBPROGRAM_VARIANT:PASS @OVERFLOW_CHECK:FAIL
   with Subprogram_Variant => (Increases => X, Increases => Y);

   function OK_3 (X, Y : Integer; B : Boolean) return Boolean is
     (if B then OK_2 (X + 1, Y - 6, B) --@SUBPROGRAM_VARIANT:NONE @OVERFLOW_CHECK:FAIL
      else OK_3 (X, Y + 1, B)) --@SUBPROGRAM_VARIANT:PASS @OVERFLOW_CHECK:FAIL
   with Subprogram_Variant => (Increases => X, Increases => Y);

   function Warn (X : Natural) return Boolean is
     (True)
     with Subprogram_Variant => (Decreases => X);

   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function Length (L : access constant List) return Natural with
     Subprogram_Variant => (Decreases => (if L = null then 0 else Length (L.N))), --@SUBPROGRAM_VARIANT:FAIL
     Annotate => (GNATprove, Terminating);

   function Length (L : access constant List) return Natural is
     (if L = null then 0 elsif Length (L.N) = Integer'Last then Integer'Last else Length (L.N) + 1);
begin
   null;
end Test_Bad_Variant;
