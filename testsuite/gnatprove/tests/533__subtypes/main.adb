procedure Main with SPARK_Mode is
   package P1 is
      type T is private;
   private
      type T is range 1 .. 5 with
        Default_Value => 4; --  @RANGE_CHECK:FAIL

      subtype S is T'Base range -3 .. 3;

      X : S;
   end P1;

   package P2 is
      type T is private;
   private
      type T is range 1 .. 5 with
        Default_Value => 4; --  @RANGE_CHECK:FAIL

      subtype S is T range 1 .. 3;

      X : S;
   end P2;

   package P3 is
      type T is private;
   private
      function Rand (X : Integer) return Integer with
        Import,
        Global => null;

      type T (B : Boolean := False) is record
         case B is
         when True =>
            X : Positive := Rand (1); --  @RANGE_CHECK:FAIL
         when False =>
            null;
         end case;
      end record;

      subtype S is T (True);

      X : S;
   end P3;
begin
   null;
end Main;
