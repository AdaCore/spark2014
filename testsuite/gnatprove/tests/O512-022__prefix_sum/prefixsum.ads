with Types; use Types;

package PrefixSum is pragma SPARK_Mode (On);

   Maximum : constant := 1_000_000;

   function All_Elements_In (A : Input; Max : Positive) return Boolean is
      (for all K in A'Range => A (K) in -Max .. Max);

   function All_Left_Elements_In (A : Input; Right : Integer; Max : Positive)
     return Boolean
   is
      (for all K in A'Range => (if K < Right then A (K) in -Max .. Max));

   function All_Right_Elements_In (A : Input; Left : Integer; Max : Positive)
     return Boolean
   is
      (for all K in A'Range => (if K > Left then A (K) in -Max .. Max));

   function Intermediate_Form (A, B : Input) return Boolean with
     Pre => All_Elements_In (A, Maximum * 8)
       and then All_Elements_In (B, Maximum);

   function Intermediate_Form (A, B : Input) return Boolean is
       (for all K in A'Range =>
          (if (K + 1) mod 8 = 0 then
             A (K) = B (0) + B (1) + B (2) + B (3) +
                     B (4) + B (5) + B (6) + B (7)
          elsif (K + 1) mod 4 = 0 then
             A (K) = B (K) + B (K-1) + B (K-2) + B (K-3)
          elsif (K + 1) mod 2 = 0 then
             A (K) = B (K) + B (K-1)
          else
             A (K) = B (K)));

   procedure Upsweep (A : in out Input; Output_Space : out Positive) with
     Pre  => All_Elements_In (A, Maximum),
     Post => All_Elements_In (A, 8 * Maximum)
       and then Output_Space = 8
       and then Intermediate_Form (A, A'Old);

   procedure Downsweep
     (Ghost : Input; A : in out Input; Input_Space : in Positive)
   with
     Pre => All_Elements_In (Ghost, Maximum)
       and then All_Elements_In (A, 8 * Maximum)
       and then Input_Space = 8
       and then Intermediate_Form (A, Ghost),
     Post =>
       A (0) = 0
         and then
       A (1) = Ghost (0)
         and then
       A (2) = Ghost (0) + Ghost (1)
         and then
       A (3) = Ghost (0) + Ghost (1) + Ghost (2)
         and then
       A (4) = Ghost (0) + Ghost (1) + Ghost (2) + Ghost (3)
         and then
       A (5) = Ghost (0) + Ghost (1) + Ghost (2) + Ghost (3) + Ghost (4)
         and then
       A (6) = Ghost (0) + Ghost (1) + Ghost (2) + Ghost (3) + Ghost (4)
             + Ghost (5)
         and then
       A (7) = Ghost (0) + Ghost (1) + Ghost (2) + Ghost (3) + Ghost (4)
             + Ghost (5) + Ghost (6);

end PrefixSum;
