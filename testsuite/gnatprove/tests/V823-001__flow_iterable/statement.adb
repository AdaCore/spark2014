with Interfaces; use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Statement with SPARK_Mode is
   package AbstractVector is
      type Vector  is private
         with Iterable => (
               First       => First,
               Next        => Next,
               Has_Element => Has_Index);

      function Length (M : Vector) return Big_Natural
      with Annotate => (GNATprove, Always_Return);

      function First (M : Vector) return Big_Natural;
      function Next (M : Vector; I : Big_Natural) return Big_Natural;
      function Has_Index (M : Vector; I : Big_Natural) return Boolean;

   private

      type Vector is record
         Length : Big_Natural := 0;
      end record;

      function First (M : Vector) return Big_Natural is (0);
      function Next (M : Vector; I : Big_Natural) return Big_Natural is (I + 1);
      function Has_Index (M : Vector; I : Big_Natural) return Boolean is (I < Length(M));

   end AbstractVector;

   package body AbstractVector is
      function Length (M : Vector) return Big_Natural is
         Cnt : Big_Natural := 0;
      begin
         for E in M loop
            Cnt := Cnt + 1;
         end loop;

         return Cnt;
      end;
   end;

begin
   null;
end;
