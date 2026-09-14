pragma Ada_2022;

procedure Bad_22 with Global => null, SPARK_Mode is
   type Matrix is array (Positive range <>, Positive range <>) of Integer;

   procedure Test (A : Matrix) is
   begin
      for E of A loop
         declare
            subtype S1 is Positive range 1 .. E'Loop_Index (1) with Ghost;
            subtype S2 is Positive range 1 .. E'Loop_Index (2) with Ghost;
            function F1 return Integer is (S1'Last) with Ghost, Global => null;
            function F2 return Integer is (S2'Last) with Ghost, Global => null;
         begin
            pragma Assert (F1 in A'Range (1));
            pragma Assert (F2 in A'Range (2));
         end;
      end loop;
   end;
begin
   null;
end;
