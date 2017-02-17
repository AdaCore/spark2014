package body PrefixSum_General is pragma SPARK_Mode (On);

   procedure Upsweep (A : in out Input; Output_Space : out Positive) is
      Space : Positive := 1;
      Left  : Natural;
      Right : Natural;
      A_Old : constant Input := A;
   begin
      while Space < A'Length loop
         Left := Space - 1;

         pragma Loop_Invariant
           (A'Length mod Space = 0
              and then
            2 * Space <= A'Length
              and then
            not Is_Even (Left + Space)
              and then
            Left < Space
              and then
            (Left + 1) mod Space = 0
              and then
            (for all K in A'Range =>
              A (K) in -Maximum * Space .. Maximum * Space)
              and then
            (for all K in A'Range =>
              (if Is_Even (K) then A (K) = A'Loop_Entry (K)))
              and then
            (for all K in A'Range =>
              (if (K + 1) mod Space = 0 then
                A (K) = Summation (A'Loop_Entry, K + 1 - Space, K))));
         pragma Loop_Variant (Increases => Space);

         while Left + Space < A'Length loop
            pragma Loop_Invariant
              (Left + Space < A'Length
                 and then
               A'Length mod Space = 0
                 and then
               2 * Space <= A'Length
                 and then
               not Is_Even (Left + Space)
                 and then
               (Left + 1) mod Space = 0
                 and then
               (for all K in A'Range =>
                 (if K < Left then
                   A (K) in -Maximum * Space * 2 .. Maximum * Space * 2
                  else
                   A (K) in -Maximum * Space .. Maximum * Space))
                 and then
               (for all K in A'Range =>
                 (if Is_Even (K) then A (K) = A'Loop_Entry (K)))
                 and then
               (for all K in A'Range =>
                 (if K < Left and (K + 1) mod (Space * 2) = 0 then
                   A (K) = Summation (A_Old, K + 1 - Space * 2, K)
                 elsif Left <= K and (K + 1) mod Space = 0 then
                   A (K) = Summation (A_Old, K + 1 - Space, K)))
                 and then
               A (Left) = Summation (A_Old, Left + 1 - Space, Left)
                 and then
               A (Left + Space) = Summation (A_Old, Left + 1, Left + Space));
            pragma Loop_Variant (Increases => Left);

            Right     := Left + Space;
            A (Right) := A (Left) + A (Right);
            Left      := Left + Space * 2;
         end loop;
         Space := Space * 2;
      end loop;
      Output_Space := Space;
   end Upsweep;

   procedure Downsweep
     (Ghost : Input; A : in out Input; Input_Space : in Positive)
   is
      Space : Natural := Input_Space;
      Left  : Natural;
      Right : Natural;
      Temp  : Integer;
   begin
      A (A'Last) := 0;
      Space      := Space / 2;

      while Space > 0 loop
         pragma Loop_Variant (Decreases => Space);

         Right := Space * 2 - 1;
         while Right < A'Length loop
            pragma Loop_Variant (Increases => Right);

            Left      := Right - Space;
            Temp      := A (Right);
            A (Right) := A (Left) + A (Right);
            A (Left)  := Temp;
            Right     := Right + Space * 2;
         end loop;
         Space := Space / 2;
      end loop;
   end Downsweep;

   function Summation (A : Input; Start_Pos, End_Pos : Index) return Integer is

      --  We use an intermediate recursive function so that an axiom is
      --  generated for Summation's postcondition.

      function Rec_Summation (A : Input;
                              Start_Pos,
                              End_Pos : Index)
                              return Integer
      with
        Pre  => Start_Pos <= End_Pos,
        Post => (if Start_Pos = End_Pos then
                   Rec_Summation'Result = A (Start_Pos));
      pragma Annotate (GNATprove, Terminating, Rec_Summation);
      function Rec_Summation (A : Input;
                              Start_Pos,
                              End_Pos : Index)
                              return Integer
      is
        (if Start_Pos = End_Pos then A (Start_Pos)
         else A (End_Pos) + Rec_Summation (A, Start_Pos, End_Pos - 1));

   begin
      return Rec_Summation (A, Start_Pos, End_Pos);
   end Summation;

end PrefixSum_General;
