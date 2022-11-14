with Parent; use Parent;
package Child with
  SPARK_Mode
is
   type D is private;
   procedure P (X : D) with Pre => False;  -- @WEAKER_PRE:FAIL
   procedure Q (X : D) with Pre => False;  -- @TRIVIAL_PRE:FAIL
   function Get return T'Class;
private
   type D is new T with null record;
   function Get return T'Class is (T'Class(D'(null record)));
end Child;
