pragma Extensions_Allowed (All_Extensions);

package Test
with SPARK_Mode
is
   type R2 is record
      X : Boolean;
      Y : Boolean;
   end record;

   type R3 is null record;

   type RR is record
      A : Integer;
      B : R2;
      C : R3;
   end record;

   procedure Run
     (A1, A2 : Integer;
      X1, X2, Y1, Y2 : Boolean;
      O      : out RR)
   with Depends => (O => (A1, X1, Y1), null => (A2, X2, Y2));
end Test;
