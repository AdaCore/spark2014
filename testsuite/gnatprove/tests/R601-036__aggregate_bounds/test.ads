package Test
is

   type Pos_Type is record
      First : Natural;
   end record;

   function Get_Pos (P : Pos_Type) return Natural;

   procedure Set (P : Pos_Type; D : out String)
   with
      Post => D = (Get_Pos (P) .. D'Last => Character'Val (0));

private

   function Get_Pos (P : Pos_Type) return Natural
   is (P.First);

end Test;
