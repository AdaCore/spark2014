package Queen with SPARK_Mode is

   -------------------------------------------------------
   --         SPARK 2014 - Queen Example                --
   --                                                   --
   -- This example illustrates the use of quantifiers   --
   -- in SPARK 2014. In this example an array is used   --
   -- to store a partial solution to the N queens       --
   -- problem.                                          --
   --                                                   --
   --  This is problem 4 of the VSTTE 2010 Competition. --
   --                                                   --
   --  https://sites.google.com/a/vscomp.org/main/      --
   --                                                   --
   -------------------------------------------------------

   N : constant Positive := 8;
   subtype Index is Positive range 1 .. N;
   type Board is array (Index) of Index;

   function Consistent_Index (B : Board; I1 : Index; I2 : Index)
                         return Boolean is
        (B (I1) /= B (I2) and then
           I1 - I2 /= B (I1) - B (I2) and then
           I1 - I2 /= B (I2) - B (I1));

   function Consistent (B : Board; K : Index) return Boolean is
     (for all I in Index'First .. K =>
        (for all J in Index'First .. I - 1 =>
             (B (I) /= B (J) and then
              I - J /= B (I) - B (J) and then
              I - J /= B (J) - B (I))));

   procedure Add_next (B : in out Board; I : Index; Done : in out Boolean;
                             C : in Board)
   with
     Pre => (not Done) and
     (for all J in Index'First .. I => C(J) = B(J)) and
     (if I > 1 then Consistent (B, I - 1)),
     Post => (if Done then Consistent (B, N) else not Consistent (C, N)) and
     (for all J in Index'First .. I => B(J) = B'Old (J))
   ;

  function Copy_Until (B : in Board; I : Index; C : in Board) return Board
  with Post => (for all J in Index'First .. I => Copy_Until'Result (J) = B(J));

   procedure Try_Row (B : in out Board; I : Index; Done : in out Boolean;
                      C : in Board)
   with Pre => (not Done) and
     (for all J in Index'First .. I-1 => C(J) = B(J)) and
     (if I > 1 then Consistent (B, I - 1)),
     Post => (if Done then Consistent (B, N) else not Consistent (C, N)) and
     (for all J in Index'First .. I-1 => B(J) = B'Old (J))
   ;

end Queen;
