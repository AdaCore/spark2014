pragma Ada_2022;

with Ada.Text_IO; use Ada.Text_IO;

with SPARK.Containers.Formal.Unbounded_Vectors;

procedure Bug_Iterator with SPARK_Mode => On is
   package String_Vectors is new SPARK.Containers.Formal.Unbounded_Vectors
      (Index_Type => Positive, Element_Type => String);

   use String_Vectors;

   V : String_Vectors.Vector;
begin
   Append (V, "Hello");
   for S of V loop
      if S'Length > 0 then
         Put_Line (S);
      end if;
   end loop;
end Bug_Iterator;
