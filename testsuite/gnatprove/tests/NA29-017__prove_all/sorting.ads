package Sorting
is
  type Int_Array is array (Natural range <>) of Integer;

   function Sorted
     (A : Int_Array;
      A_First, Length : Natural)
     return Boolean
     with Ghost, Import, Global => null, Annotate => (GNATprove, Always_Return);

   function Perm
     (A, B : Int_Array;
      A_First, Length : Natural)
     return Boolean
     with Ghost, Import, Global => null, Annotate => (GNATprove, Always_Return);

  procedure Mergesort
    (A       : in out Int_Array;
     A_First : in     Natural;
     Length  : in     Natural;
     B       : in out Int_Array)
     with Depends => ((A, B) => (A, A_First, B, Length)),
          Pre     =>  A'First <= A_First and A_First + Length <= A'Last + 1 and Length <= B'Length,
          Post    =>  Sorted (A, A_First, Length) and Perm (A'Old, A, A_First, Length);

end Sorting;
