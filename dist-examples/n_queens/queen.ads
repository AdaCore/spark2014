package Queen is

   N : constant Positive := 8;
   subtype Index is Positive range 1 .. N;
   type Board is array (Index) of Index;

   function Consistent_Index (B : Board; I1 : Index; I2 : Index)
                         return Boolean is
        (B (I1) /= B (I2) and then
           I1 - I2 /= B (I1) - B (I2) and then
           I1 - I2 /= B (I2) - B (I1));

   function Consistent (B : Board; I : Index) return Boolean is
           (for all J in Index'First .. I - 1 =>
              Consistent_Index (B, I, J));

   procedure Add_next (B : in out Board; I : Index; Done : in out Boolean;
                             C : in Board)
   with Pre => (not Done) and
           (for all J in Index'First .. I => C(J) = B(J)) and
           (for all J in Index'First .. I-1 => Consistent (B, J)),
        Post => (if Done then
                   (for all J in Index'First .. N => Consistent (B, J))) and
           (for all J in Index'First .. I => B(J) = B'Old (J)) and
           (if not Done then
              not (for all J in I .. N => Consistent (C, J)))
         ;

   procedure Try_Row (B : in out Board; I : Index; Done : in out Boolean;
                      C : in Board)
   with Pre => (not Done) and
           (for all J in Index'First .. I-1 => C(J) = B(J)) and
           (for all J in Index'First .. I-1 => Consistent (B, J)),
        Post => (if Done then
                    (for all J in Index'First .. N => Consistent (B, J))) and
           (for all J in Index'First .. I-1 => B(J) = B'Old (J)) and
           (if not Done then
              not (for all J in I .. N => Consistent (C, J)))
         ;

end Queen;
