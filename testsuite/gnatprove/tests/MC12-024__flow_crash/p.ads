with Interfaces;
package P
  with SPARK_Mode => On
is
   R_Size : constant := 64;
   type R is record
      A : Integer;
      B : Float;
   end record;
   for R'Size use R_Size;

   subtype R_Raw_Index is Positive range 1 .. 8;

   type R_Raw_Vector is array (R_Raw_Index) of Interfaces.Unsigned_8;
   for R_Raw_Vector'Size use R_Size;

   Null_R : constant R := R'(0, 0.0);
   Null_Raw_R : constant R_Raw_Vector := R_Raw_Vector'(others => 0);

   Full_S : R;
   Raw_S  : R_Raw_Vector;
   for Raw_S'Address use Full_S'Address;

   procedure Initialize
     with Global  => (Output => (Full_S, Raw_S)),
          Depends => ((Full_S, Raw_S) => null),
          Post    => Full_S = Null_R and
                     Raw_S  = Null_Raw_R;

   procedure Update_R (X : in Integer;
                       Y : in Float)
     with Global => (In_Out => (Full_S, Raw_S)),
          Depends => ((Full_S, Raw_S) => +(X, Y));

end P;

