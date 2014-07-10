package body Set_Ops
  with SPARK_Mode
is

   function Lemma_Members_Copied (Source : Set;
                                  Count : Natural;
                                  Original_Dest : Set;
                                  Dest : Set) return Boolean is
     (Number_Of_Members (Original_Dest) = 0 and then
      (for all I in 1 .. Count =>
            Is_Member (Dest, Get_Member (Source, I))) and then
      (for all J in 1 .. Number_Of_Members (Dest) =>
            Is_Member (Source, Get_Member (Dest, J)))) with
   Pre => Count <= Number_Of_Members (Source) and
     Number_Of_Members (Original_Dest) = 0,
   Post => (if Count = Number_Of_Members (Source) then
               Lemma_Members_Copied'Result = (Source = Dest));

   function Lemma_Members_Unioned (Source : Set;
                                   Count : Natural;
                                   Origin : Set;
                                   Target : Set) return Boolean is
     ((for all I in 1 .. Number_Of_Members (Origin) =>
           Is_Member (Target, Get_Member (Origin, I))) and then
        (for all J in 1 .. Count =>
              Is_Member (Target, Get_Member (Source, J))) and then
        (for all K in 1 .. Number_Of_Members (Target) =>
              Is_Member (Source, Get_Member (Target, K)) or else
              Is_Member (Origin, Get_Member (Target, K)))) with
   Pre => Count <= Number_Of_Members (Source),
   Post => (if Count = Number_Of_Members (Source) then
               Lemma_Members_Unioned'Result =
                 Is_Union (Origin, Source, Target));

   function Lemma_Members_Intersecting (Source : Set;
                                        Count : Natural;
                                        Origin : Set;
                                        Target : Set) return Boolean is
     (((Number_Of_Members (Origin) = 0 or else
        Number_Of_Members (Source) = 0) and then
          Number_Of_Members (Target) = 0) or else
      ((for all I in 1 .. Count =>
           (if Is_Member (Origin, Get_Member (Source, I)) then
              Is_Member (Target, Get_Member (Source, I)))) and then
      (for all K in 1 .. Number_Of_Members (Target) =>
           Is_Member (Source, Get_Member (Target, K)) and then
           Is_Member (Origin, Get_Member (Target, K))))) with
   Pre => Count <= Number_Of_Members (Source),
   Post => (if Count = Number_Of_Members (Source) then
               Lemma_Members_Intersecting'Result =
                 Is_Intersection (Origin, Source, Target));

   function Lemma_Members_Difference (Origin : Set;
                                      Count : Natural;
                                      Exclude : Set;
                                      Target : Set) return Boolean is

      ((for all I in 1 .. Count =>
           (if not Is_Member (Exclude, Get_Member (Origin, I)) then
              Is_Member (Target, Get_Member (Origin, I)))) and then
      (for all K in 1 .. Number_Of_Members (Target) =>
           Is_Member (Origin, Get_Member (Target, K)) and then
           not Is_Member (Exclude, Get_Member (Target, K)))) with
   Pre => Count <= Number_Of_Members (Origin),
   Post => (if Count = Number_Of_Members (Origin) then
               Lemma_Members_Difference'Result =
                 Is_Difference (Origin, Exclude, Target));

   procedure Copy_Set (Source : in Set; Dest : out Set) with
     Post => Source = Dest
   is
   begin
      Destroy_Set (Dest);
      for I in 1 .. Number_Of_Members (Source) loop
         Add_Member (Dest, Get_Member (Source, I));
         pragma Assume (Lemma_Members_Copied (Source => Source,
                                              Count  => I,
                                              Original_Dest => Dest'Loop_Entry,
                                              Dest => Dest));
      end loop;
   end Copy_Set;

   -----------
   -- Union --
   -----------

   procedure Union (A, B : in Set; C : out Set) is
   begin
      Copy_Set (A, C);
      for J in 1 .. Number_Of_Members (B) loop
         Add_Member (C, Get_Member (B, J));
         pragma Assume (Lemma_Members_Unioned (B, J, A, C));
      end loop;
   end Union;

   procedure Union (United : in out Set; B : in Set) is
   begin
      for I in 1 .. Number_Of_Members (B) loop
         Add_Member (United, Get_Member (B, I));
      end loop;
   end Union;

   ------------------
   -- Intersection --
   ------------------

   procedure Intersection (A, B : Set; C : out Set) is
      Next_Member : Integer;
   begin
      Destroy_Set (C);
      for I in 1 .. Number_Of_Members (B) loop
         Next_Member := Get_Member (B, I);
         if Is_Member (A, Next_Member) then
            Add_Member (C, Next_Member);
         end if;
         pragma Assume (Lemma_Members_Intersecting (Source => B,
                                                    Count  => I,
                                                    Origin => A,
                                                    Target => C));
      end loop;
   end Intersection;

   procedure Intersection (Intersects : in out Set; B : in Set) is
      Temp_Set : Set;
   begin
      Copy_Set (Intersects, Temp_Set);
      Intersection (Temp_Set, B, Intersects);
   end Intersection;

   ----------------
   -- Difference --
   ----------------

   procedure Difference (A, B : in Set; C : out Set) is
      Next_Member : Integer;
   begin
      Destroy_Set (C);
      for I in 1 .. Number_Of_Members (A) loop
         Next_Member := Get_Member (A,I);
         if not Is_Member (B, Next_Member) then
            Add_Member (C, Next_Member);
         end if;
         pragma Assume (Lemma_Members_Difference (Origin  => A,
                                                  Count   => I,
                                                  Exclude => B,
                                                  Target  => C));
      end loop;
   end Difference;

   procedure Difference (Diff : in out Set; B : in Set) is
      Temp_Set : Set;
   begin
      Copy_Set (Diff, Temp_Set);
      Difference (Temp_Set, B, Diff);
   end Difference;

end Set_Ops;
