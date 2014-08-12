with Ada.Unchecked_Conversion;

package body Conversions_Of_Records
is
   type Rec_A is record
      X : Integer;
      F : Boolean;
   end record;

   type Rec_B is record
      A : Short_Integer;
      B : Short_Integer;
      G : Boolean;
   end record;

   type Rec_C is new Rec_A;

   subtype Rec_D is Rec_A;

   function To_Rec_B is new Ada.Unchecked_Conversion (Source => Rec_A,
                                                      Target => Rec_B);

   procedure Test_01_OK (X1 : in     Integer;
                         X2 : in     Boolean;
                         Y1 :    out Short_Integer;
                         Y2 :    out Short_Integer)
   with Depends => (Y1 => (X1, X2),
                    Y2 => (X1, X2))
   is
      R : Rec_A := (X1, X2);
   begin
      Y1 := To_Rec_B (R).A;
      Y2 := To_Rec_B (R).B;
   end Test_01_Ok;

   procedure Test_02_OK (X1 : in     Integer;
                         X2 : in     Boolean;
                         Y1 :    out Integer;
                         Y2 :    out Boolean)
   with Depends => (Y1 => (X1, X2),
                    Y2 => (X1, X2))
   is
      R : Rec_A := (X1, X2);
   begin
      Y1 := Rec_C (R).X;
      Y2 := Rec_C (R).F;
   end Test_02_Ok;

   procedure Test_03_OK (X1 : in     Integer;
                         X2 : in     Boolean;
                         Y1 :    out Integer;
                         Y2 :    out Boolean)
   with Depends => (Y1 => X1,
                    Y2 => X2)
   is
      R : Rec_A := (X1, X2);
   begin
      Y1 := Rec_D (R).X;
      Y2 := Rec_D (R).F;
   end Test_03_Ok;

end Conversions_Of_Records;
