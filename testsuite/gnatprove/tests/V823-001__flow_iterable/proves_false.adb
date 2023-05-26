with Interfaces; use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Proves_False with SPARK_Mode is
   generic
      type Value_Type is private;
   package AbstractVector2  is
      type Vector  is private
         with Iterable => (
               First => Iter_First,
               Next => Iter_Next,
               Has_Element => Has_Index);

      function Length (M : Vector) return Big_Natural
      with Post =>
         (for some k in M => k = Length'Result - 1) and then --@POSTCONDITION:FAIL --@TERMINATION:CHECK
         (for all k in M => k < Length'Result);

      function Iter_First (M : Vector) return Big_Natural;
      function Iter_Next (M : Vector; I : Big_Natural) return Big_Natural;
      function Has_Index (M : Vector; I : Big_Natural) return Boolean;

      function Empty return Vector
         with Post => Length(Empty'Result) = 0;

   private

      type Vector
      is record
         Length : Big_Natural := 0;
      end record;

      function Length (M : Vector) return Big_Natural is (M.Length);

      function Iter_First (M : Vector) return Big_Natural is (0);
      function Iter_Next (M : Vector; I : Big_Natural) return Big_Natural is (I + 1);
      function Has_Index (M : Vector; I : Big_Natural) return Boolean is (I < Length(M)); --@TERMINATION:CHECK

      function Empty return Vector is (Vector'( Length => 0 ));
   end AbstractVector2;

   package NaturalVector is new AbstractVector2(Unsigned_64);
   use NaturalVector;

   procedure Test is
   begin
      pragma Assert(NaturalVector.Length(NaturalVector.Empty) = 1);
      pragma Assert(False); --  This is proved, but we emit a check for termination of Length
   end;

begin
   null;
end Proves_False;
