pragma Ada_2022;

with SPARK.Containers.Formal.Vectors;

procedure Main with SPARK_Mode is

   package Vectors is new SPARK.Containers.Formal.Vectors (Positive, Integer);
   use Vectors;

   procedure Test_Bad (V : Vectors.Vector) with Post => True;
   procedure Test_Bad (V : Vectors.Vector) is
   begin
      for E of V loop
         declare
            subtype S is Integer range 1 .. E'Loop_Index with Ghost;
         begin
            pragma Assert (E in S'Range); -- @ASSERT:FAIL
         end;
      end loop;
   end Test_Bad;

   procedure Test_OK (V : Vectors.Vector) with
     Pre =>
       (for all I in 1 .. Last_Index (V) => Element (V, I) in 1 .. I);
   procedure Test_OK (V : Vectors.Vector) is
   begin
      for E of V loop
         declare
            subtype S is Integer range 1 .. E'Loop_Index with Ghost;
         begin
            pragma Assert (E in S'Range); -- @ASSERT:PASS
         end;
      end loop;
   end Test_OK;

begin
   null;
end Main;
