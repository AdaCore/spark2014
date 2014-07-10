with Simple_Sets;
use Simple_Sets;

package Set_Ops
  with SPARK_Mode
is

   function Is_Union (A, B, A_Union : Set) return Boolean is
     ((for all I in 1 .. Number_Of_Members (A_Union) =>
            Is_Member (A, Get_Member (A_Union, I)) or else
            Is_Member (B, Get_Member (A_Union, I))) and then
        (for all J in 1 .. Number_Of_Members (A) =>
            Is_Member (A_Union, Get_Member (A, J))) and then
        (for all K in 1 .. Number_Of_Members (B) =>
            Is_Member (A_Union, Get_Member (B, K))));

   function Is_Intersection (A, B, An_Intersect : Set) return Boolean is
     ((((Number_Of_Members (A) = 0 or else Number_Of_Members (B) = 0) and then
          Number_Of_Members (An_Intersect) = 0)) or else
        ((for all I in 1 .. Number_Of_Members (An_Intersect) =>
           Is_Member (A, Get_Member (An_Intersect, I)) and then
           Is_Member (B, Get_Member (An_Intersect, I))) and then
        (for all J in 1 .. Number_Of_Members (B) =>
             (if Is_Member (A, Get_Member (B, J)) then
                   Is_Member (An_Intersect, Get_Member (B, J))))));

   function Is_Difference (A, B, A_Difference : Set) return Boolean is
     ((for all I in 1 .. Number_Of_Members (A_Difference) =>
           Is_Member (A, Get_Member (A_Difference, I)) and then
         not Is_Member (B, Get_Member (A_Difference, I))) and then
          (for all J in 1 .. Number_Of_Members (A) =>
             (if not Is_Member (B, Get_Member (A, J)) then
                 Is_Member (A_Difference, Get_Member (A, J)))));

   procedure Union (A, B : in Set; C : out Set) with
      Post => Is_Union (A, B, C);

   procedure Union (United : in out Set; B : in Set);

   procedure Intersection (A, B : Set; C : out Set) with
      Post => Is_Intersection (A, B, C);

   procedure Intersection (Intersects : in out Set; B : in Set);

   procedure Difference (A, B : in Set; C : out Set) with
      Post => Is_Difference (A, B, C);

   procedure Difference (Diff : in out Set; B : in Set);


end Set_Ops;
