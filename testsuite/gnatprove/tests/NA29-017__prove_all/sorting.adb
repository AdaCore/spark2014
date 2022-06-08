package body Sorting
is

   function Perm2
     (A, B : Int_Array;
      A_First1, A_First2, B_First, A_Length1, A_Length2 : Natural)
     return Boolean
     with Ghost, Import, Global => null, Annotate => (GNATprove, Always_Return);

   function Le_Array
     (A, B : Int_Array;
      A_First, B_First, A_Length, B_Length : Natural)
     return Boolean
     with Ghost, Import, Global => null, Annotate => (GNATprove, Always_Return);

  ------------------------------------------------------------------------------

  procedure Copy
    (A       : in     Int_Array;
     B       : in out Int_Array;
     A_First : in     Natural;
     Length  : in     Natural;
     B_First : in     Natural)
    with
      Depends => (B =>+ (A, A_First, B_First, Length)),
      Pre =>
         A'First <= A_First and
         A_First + Length <= A'Last + 1 and
         B'First <= B_First and
         B_First + Length <= B'Last + 1,
      Post => (for all J in Natural range B'Range =>
        ((if J in B_First .. B_First + Length - 1 then
            B (J) = A (A_First + J - B_First)) and
         (if J not in B_First .. B_First + Length - 1 then
            B (J) = B'Old (J))))
  is
  begin
    for I in Natural range 0 .. Length - 1
    loop
      pragma Loop_Invariant
        (for all J in Natural range B'Range =>
           ((if J in B_First .. B_First + I - 1 then
               B (J) = A (A_First + J - B_First)) and
            (if J not in B_First .. B_First + I - 1 then
               B (J) = B'Loop_Entry (J))));

      B (B_First + I) := A (A_First + I);
      pragma Assert_And_Cut
        (for all J in Natural range B'Range =>
           ((if J in B_First .. B_First + (I + 1) - 1 then
               B (J) = A (A_First + J - B_First)) and
            (if J not in B_First .. B_First + (I + 1) - 1 then
               B (J) = B'Loop_Entry (J))));
    end loop;
  end Copy;

  ------------------------------------------------------------------------------

  procedure Merge
    (A       : in out Int_Array;
     B       : in out Int_Array;
     A_First : in     Natural;
     Length1 : in     Natural;
     Length2 : in     Natural)
    with
      Depends => ((A, B) => (A, A_First, B, Length1, Length2)),
      Pre =>
        A'First <= A_First and A_First + Length1 + Length2 <= A'Last + 1 and
        Length1 + Length2 <= B'Length and Length1 + Length2 <= Natural'Last and
        Sorted (A, A_First, Length1) and Sorted (A, A_First + Length1, Length2) and
        B'First <= B'Last,
      Post =>
        Sorted (A, A_First, Length1 + Length2) and
        Perm (A'Old, A, A_First, Length1 + Length2) and
        (for all K in Natural range A'Range =>
           (if K not in A_First .. A_First + Length1 + Length2 - 1 then
              A (K) = A'Old (K)))
  is
    I, J : Natural;
  begin
    I := 0;
    J := 0;

    loop
       pragma Loop_Invariant
         (I <= Length1 and J <= Length2 and
          Sorted (B, B'First, I + J) and
          Perm2 (A, B, A_First, A_First + Length1, B'First, I, J) and
          Le_Array (B, A, B'First, A_First + I, I + J, Length1 - I) and
          Le_Array (B, A, B'First, A_First + Length1 + J, I + J, Length2 - J) and
          A = A'Loop_Entry);

       -- FIXME workaround for [N410-033]
       exit when not (I < Length1 or else J < Length2);

       if
         J = Length2 or else
         (I < Length1 and then A (A_First + I) <= A ((A_First + Length1) + J))
       then
          B (B'First + (I + J)) := A (A_First + I);
          I := I + 1;
       else
          B (B'First + (I + J)) := A ((A_First + Length1) + J);
          J := J + 1;
       end if;
    end loop;

    Copy (B, A, B'First, Length1 + Length2, A_First);
  end Merge;

  ------------------------------------------------------------------------------

  procedure Mergesort
    (A       : in out Int_Array;
     A_First : in     Natural;
     Length  : in     Natural;
     B       : in out Int_Array)
  is
    I, L, K : Natural;
  begin
    L := 1;

    Outer: loop
      pragma Loop_Invariant
        ((for all J in Natural =>
            (if J * L < Length then
             Sorted (A, A_First + J * L, Natural'Min (L, Length - J * L)))) and
         Perm (A'Loop_Entry(Outer), A, A_First, Length) and L >= 1);

      I := 0;

      loop
         pragma Loop_Invariant
           (I <= Length and
            (if I < Length then I mod (L * 2) = 0) and
            (for all J in Natural =>
               (if J * L * 2 < I then
                Sorted (A, A_First + J * L * 2, Natural'Min (L * 2, Length - J * L * 2)))) and
            (for all J in Natural =>
               (if J * L < Length - I then
                Sorted (A, A_First + I + J * L, Natural'Min (L, Length - I - J * L)))) and
            Perm (A'Loop_Entry(Outer), A, A_First, Length) and L >= 1);

         -- FIXME workaround for [N410-033]
         exit when not (I < Length - L);

         K := Natural'Min (L, (Length - L) - I);
         Merge (A, B, A_First + I, L, K);
         I := I + (L + K);
      end loop;

      pragma Assert_And_Cut
        ((for all J in Natural =>
            (if J * L * 2 < Length then
             Sorted (A, A_First + J * L * 2, Natural'Min (L * 2, Length - J * L * 2)))) and
         Perm (A'Loop_Entry(Outer), A, A_First, Length) and L >= 1);

      exit when Length - L <= L;
      L := 2 * L;
    end loop Outer;
  end Mergesort;

end Sorting;
