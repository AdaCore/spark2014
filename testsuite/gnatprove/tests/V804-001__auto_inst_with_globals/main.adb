with Interfaces; use Interfaces;
procedure Main with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   A : Nat_Array (1 .. 100);

   function Is_Ordered return Boolean is
     (for all I in A'Range =>
        (if I /= A'Last then A (I) <= A (I + 1)));

   procedure Lemma_Ordered with
     Ghost,
     Global => (Proof_In => A),
     Pre  => Is_Ordered,
     Post => Is_Ordered_Strong,
     Annotate => (GNATprove, Automatic_Instantiation);

   function Is_Ordered_Strong return Boolean is
     (for all I in A'Range =>
        (for all J in A'Range =>
             (if I < J then A (I) <= A (J))));

   procedure Lemma_Ordered is
   begin
      for D in 1 .. A'Length - 1 loop
         for K in A'Range loop
            for L in A'Range loop
               pragma Loop_Invariant
                 (for all J in A'First .. L =>
                    (if K < J and J - K <= D then A (K) <= A (J)));
            end loop;
            pragma Loop_Invariant
              (for all I in A'First .. K =>
                 (for all J in A'Range =>
                      (if I < J and J - I <= D then A (I) <= A (J))));
         end loop;
         pragma Loop_Invariant
           (for all I in A'Range =>
              (for all J in A'Range =>
                   (if I < J and J - I <= D then A (I) <= A (J))));
      end loop;
   end Lemma_Ordered;

   --  Check that Lemma_Ordered really is instanciated automatically
   procedure Test with
     Global => (Proof_In => A),
     Pre  => Is_Ordered,
     Post => Is_Ordered_Strong;

   procedure Test is null;

begin
   null;
end Main;
