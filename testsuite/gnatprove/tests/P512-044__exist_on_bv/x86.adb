package body X86
with SPARK_Mode
is

   -----------------------------------------------------------------------
   function InRange64(var: in Unsigned64; bottom: in Unsigned64; range_size: Unsigned64)
                      return Boolean is
   begin
      return
     (if (Bottom <= Unsigned64'Last - Range_Size) then
          (Bottom <= Var and Var <= Bottom + Range_Size)
      else
        (Bottom <= Var and Var <= Unsigned64'Last) or
          (Var <= Range_Size - (Unsigned64'Last - Bottom) - 1));
   end InRange64;
   -----------------------------------------------------------------------

   function RangesIntersect(var1: in Unsigned64; var1_range_size: in Unsigned64; var2: in Unsigned64; var2_range_size: in Unsigned64)
                            return Boolean is

      procedure Prove_Post with Ghost is
         Res : constant Boolean :=
           InRange64(var1,var2-var1_range_size,
                     var1_range_size+var2_range_size);
      begin
         if Res then
            for N in 0 .. var1_range_size+var2_range_size loop
               if var1 = (var2-var1_range_size + N) then
                  declare
                     N1 : Unsigned64;
                     N2 : Unsigned64;
                  begin
                     if N > var1_range_size then
                        N1 := 0;
                        N2 := N - var1_range_size;
                        pragma Assert (N2 <= var2_range_size);
                     elsif  N < var2_range_size then
                        N1 := var1_range_size;
                        N2 := N;
                     else
                        N1 := var1_range_size - N;
                        N2 := 0;
                     end if;

                     pragma Assert (N1 in 0 .. var1_range_size
                                    and N2 in 0 .. var2_range_size
                                    and var1 + N1 = var2 + N2);
                  end;
                  pragma Assert
                    (for some i in 0 .. var1_range_size =>
                       (for some j in 0 .. var2_range_size =>
                            (var1 + i) = (var2 + j)));
               end if;
               pragma Loop_Invariant
                 ((for all M in 0 .. N => var1 /= (var2-var1_range_size + M))
                  or (for some i in 0 .. var1_range_size =>
                          (for some j in 0 .. var2_range_size =>
                             (var1 + i) = (var2 + j))));
            end loop;
            pragma Assert (for some i in 0 .. var1_range_size =>
                             (for some j in 0 .. var2_range_size =>
                                (var1 + i) = (var2 + j)));
         else
            for N1 in 0 .. var1_range_size loop
               pragma Loop_Invariant
                 (if N1 /= 0 then
                    (for all I in 0 .. N1 - 1 =>
                         (for all J in 0 .. var2_range_size =>
                              (var1 + i /= var2 + j))));
               for N2 in 0 .. var2_range_size loop
                  declare
                     N : constant Unsigned64 := N2 + (var1_range_size - N1);
                  begin
                     pragma Assert (N in 0 .. var1_range_size+var2_range_size);
                     pragma Assert (var1 /= var2 - var1_range_size + N);
                  end;
                  pragma Assert (var1 + N1 /= var2 + N2);
                  pragma Loop_Invariant
                    (for all J in 0 .. N2 => (var1 + N1 /= var2 + J));
               end loop;
               pragma Assert
                 (for all J in 0 .. var2_range_size => (var1 + N1 /= var2 + J));
               pragma Assert (if N1 /= 0 then
                                (for all i in 0 .. N1 =>
                                   (for all j in 0 .. var2_range_size =>
                                        (var1 + i) /= (var2 + j))));
               pragma Assert (for all i in 0 .. N1 =>
                                (for all j in 0 .. var2_range_size =>
                                   (var1 + i) /= (var2 + j)));
            end loop;

            pragma Assert (for all i in 0 .. var1_range_size =>
                             (for all j in 0 .. var2_range_size =>
                                (var1 + i) /= (var2 + j)));
         end if;
      end Prove_Post;

   begin
      Prove_Post;
      return InRange64(var1,var2-var1_range_size, var1_range_size+var2_range_size);
   end RangesIntersect;

end X86;
