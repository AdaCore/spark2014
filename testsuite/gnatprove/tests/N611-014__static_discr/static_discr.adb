package body Static_Discr with SPARK_Mode is

   function Search_Max (A : Holder_Max; E : Natural) return Natural is
      procedure Search_Some (Current : in out Holder_Max;
                             Result  : out Natural)
      with
          Pre  => Current.Length in 1 .. Current.C,
          Post => Current.Content.Content = Current'Old.Content.Content
            and then Current.Length < Current'Old.Length
            and then (if Result = 0 then
                        (for all I in Current.Length + 1 .. Current'Old.Length =>
                               Current.Content.Content (I) /= E)
                      else (Result in Current.Length .. Current'Old.Length
                            and then Current.Content.Content (Result) = E));

      procedure Search_Some (Current : in out Holder_Max;
                             Result  : out Natural) is
      begin
         if Current.Content.Content (Current.Length) = E then
            Result := Current.Length;
         else
            Result := 0;
         end if;
         Current.Length := Current.Length - 1;
      end Search_Some;

      Current : Holder_Max := A;
      Result  : Natural := 0;
   begin
      while Result = 0 and then Current.Length > 0 loop
         pragma Loop_Invariant
           (Current.Length in 1 .. A.Length
            and then A.Content.Content = Current.Content.Content
            and then (for all I in Current.Length + 1 .. A.Length =>
                          A.Content.Content (I) /= E));
         pragma Assert (Current.Unused = Max);
         Search_Some (Current, Result);
         pragma Assert (Current.Unused = Max);
         pragma Assert (A.Content.Content = Current.Content.Content);
      end loop;
      return Result;
   end Search_Max;

   function Search_Array (A : Nat_Array; E : Natural) return Natural is
      type My_Holder is new Holder (A'Last, A'Last);

      procedure Search_Some (Current : in out My_Holder;
                             Result  : out Natural)
      with
          Pre  => Current.Length in 1 .. Current.C,
          Post => Current.Content.Content = Current'Old.Content.Content
            and then Current.Length < Current'Old.Length
            and then (if Result = 0 then
                        (for all I in Current.Length + 1 .. Current'Old.Length =>
                               Current.Content.Content (I) /= E)
                      else (Result in Current.Length .. Current'Old.Length
                            and then Current.Content.Content (Result) = E));

      procedure Search_Some (Current : in out My_Holder;
                             Result  : out Natural) is
      begin
         if Current.Content.Content (Current.Length) = E then
            Result := Current.Length;
         else
            Result := 0;
         end if;
         Current.Length := Current.Length - 1;
      end Search_Some;

      Current : My_Holder  := (A'Last, A'Last, (A'Last, A'Last, A), A'Last);
      Result  : Natural := 0;
   begin
      while Result = 0 and then Current.Length > 0 loop
         pragma Loop_Invariant
           (Current.Length in A'Range
            and then A = Current.Content.Content
            and then (for all I in Current.Length + 1 .. A'Last =>
                          A (I) /= E));
         pragma Assert (Current.Unused = A'Last);
         Search_Some (Current, Result);
         pragma Assert (Current.Unused = A'Last);
         pragma Assert (A = Current.Content.Content);
      end loop;
      return Result;
   end Search_Array;

   function Search (A : Holder; E : Natural) return Natural is
      procedure Search_Some (Current : in out Holder;
                             Result  : out Natural)
      with
          Pre  => Current.Length in 1 .. Current.C,
          Post => Current.Content.Content = Current'Old.Content.Content
            and then Current.Length < Current'Old.Length
            and then (if Result = 0 then
                        (for all I in Current.Length + 1 .. Current'Old.Length =>
                               Current.Content.Content (I) /= E)
                      else (Result in Current.Length .. Current'Old.Length
                            and then Current.Content.Content (Result) = E));

      procedure Search_Some (Current : in out Holder;
                             Result  : out Natural) is
      begin
         if Current.Content.Content (Current.Length) = E then
            Result := Current.Length;
         else
            Result := 0;
         end if;
         Current.Length := Current.Length - 1;
      end Search_Some;

      Current : Holder  := A;
      Result  : Natural := 0;
   begin
      while Result = 0 and then Current.Length > 0 loop
         pragma Loop_Invariant
           (Current.Length in 1 .. A.Length
            and then A.Content.Content = Current.Content.Content
            and then (for all I in Current.Length + 1 .. A.Length =>
                          A.Content.Content (I) /= E));
         pragma Assert (Current.Unused = A.Unused);
         Search_Some (Current, Result);
         pragma Assert (Current.Unused = A.Unused);
         pragma Assert (A.Content.Content = Current.Content.Content);
      end loop;
      return Result;
   end Search;

end;
