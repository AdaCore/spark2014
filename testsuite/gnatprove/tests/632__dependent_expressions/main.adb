procedure Main with SPARK_Mode is
   function Random return Integer with Import, Global => null;
   package A is
      type Root is tagged null record;
      function Translate (X : Root; Control : Root) return Root
        with Import, Global => null;
      function Label (X : root) return Integer with Import, Global => null;
      procedure Test_If (X : Root; Y : out Boolean)
        with Import, Global => null,
          Post'Class => Y =
            (X = (if Translate (X,X) = X then X else Translate (Translate (X,X),X)));
      procedure Test_Case (X : Root; Y : Integer; Z : out Boolean)
        with Import, Global => null,
          Post'Class =>
            Z = (X = (case Y is
                      when 0 => X,
                      when 1 => Translate (X,X),
                      when 2 => Translate (Translate (X,X),X),
                      when 3 => Translate (Translate (Translate (X,X),X),X),
                      when others => X));
      procedure Test_Declare (X : Root; Y : out Boolean)
        with Import, GLobal => null,
          Post'Class =>
            Y = (X = (declare
                   U : constant Integer := Label (X);
                 begin
                 (if U = 0 then X else Translate (X,X))));

   end A;
   use A;
   package B is
      type Child is new Root with record Field : Integer; end record;
      overriding function Translate (X : Child; Control : Child) return Child is
         (Child'(Field =>
                     (if X.Field = 0 then X.Field - 1
                      elsif X.Field = 42 then 42
                      else X.Field + 1)));
      overriding function Label (X : Child) return Integer is (1);
      overriding procedure Test_If (X : Child; Y : out Boolean)
        with Import, Global => null;
      overriding procedure Test_Case (X : Child; Y : Integer; Z : out Boolean)
        with Import, Global => null;
      overriding procedure Test_Declare (X : Child; Y : out Boolean)
        with Import, Global => null;
   end B;
   use B;
   Out_B : Boolean;
   X : Root'Class := Child'(Field => 0);
   Y : Root'Class := Child'(Field => -1);
   Z : Root'Class := Child'(Field => 42);
   T : Root'Class := Child'(Field => 36);
begin
   case Random is
      when 0 =>
         Test_If (X, Out_B);
         pragma Assert (Out_B); --@ASSERT:PASS
      when 1 =>
         Test_If (Y, Out_B);
         pragma Assert (Out_B); --@ASSERT:PASS
      when 2 =>
         Test_If (Z, Out_B);
         pragma Assert (Out_B); --@ASSERT:PASS
      when 3 =>
         Test_If (T, Out_B);
         pragma Assert (Out_B); --@ASSERT:FAIL
      when 4 =>
         declare
            Field : Integer with Import;
            U : Root'Class := Child'(Field => Field);
         begin
            Test_Case (U, 0, Out_B);
            pragma Assert (Out_B); --@ASSERT:PASS
         end;
      when 5 =>
         Test_Case (Z, 1, Out_B);
         pragma Assert (Out_B); --@ASSERT:PASS
         Test_Case (X, 1, Out_B);
         pragma Assert (Out_B); --@ASSERT:FAIL
      when 6 =>
         Test_Case (Z, 2, Out_B);
         pragma Assert (Out_B); --@ASSERT:PASS
         Test_Case (X, 2, Out_B);
         pragma Assert (Out_B); --@ASSERT:PASS
         Test_Case (Y, 2, Out_B);
         pragma Assert (Out_B); --@ASSERT:PASS
         Test_Case (T, 2, Out_B);
         pragma Assert (Out_B); --@ASSERT:FAIL
      when 7 =>
         Test_Case (Z, 3, Out_B);
         pragma Assert (Out_B); --@ASSERT:PASS
         Test_Case (X, 3, Out_B);
         pragma Assert (Out_B); --@ASSERT:FAIL
      when 8 =>
         Test_Declare (Z, Out_B);
         pragma Assert (Out_B); --@ASSERT:PASS
         Test_Declare (Y, Out_B);
         pragma Assert (Out_B); --@ASSERT:FAIL
      when others => null;
   end case;
end Main;
